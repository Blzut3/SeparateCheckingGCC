// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package reflect

import (
	"math"
	"runtime"
	"strconv"
	"unsafe"
)

const bigEndian = false // can be smarter if we find a big-endian machine
const ptrSize = unsafe.Sizeof((*byte)(nil))
const cannotSet = "cannot set value obtained from unexported struct field"

// TODO: This will have to go away when
// the new gc goes in.
func memmove(adst, asrc unsafe.Pointer, n uintptr) {
	dst := uintptr(adst)
	src := uintptr(asrc)
	switch {
	case src < dst && src+n > dst:
		// byte copy backward
		// careful: i is unsigned
		for i := n; i > 0; {
			i--
			*(*byte)(unsafe.Pointer(dst + i)) = *(*byte)(unsafe.Pointer(src + i))
		}
	case (n|src|dst)&(ptrSize-1) != 0:
		// byte copy forward
		for i := uintptr(0); i < n; i++ {
			*(*byte)(unsafe.Pointer(dst + i)) = *(*byte)(unsafe.Pointer(src + i))
		}
	default:
		// word copy forward
		for i := uintptr(0); i < n; i += ptrSize {
			*(*uintptr)(unsafe.Pointer(dst + i)) = *(*uintptr)(unsafe.Pointer(src + i))
		}
	}
}

// Value is the reflection interface to a Go value.
//
// Not all methods apply to all kinds of values.  Restrictions,
// if any, are noted in the documentation for each method.
// Use the Kind method to find out the kind of value before
// calling kind-specific methods.  Calling a method
// inappropriate to the kind of type causes a run time panic.
//
// The zero Value represents no value.
// Its IsValid method returns false, its Kind method returns Invalid,
// its String method returns "<invalid Value>", and all other methods panic.
// Most functions and methods never return an invalid value.
// If one does, its documentation states the conditions explicitly.
//
// A Value can be used concurrently by multiple goroutines provided that
// the underlying Go value can be used concurrently for the equivalent
// direct operations.
type Value struct {
	// typ holds the type of the value represented by a Value.
	typ *rtype

	// Pointer-valued data or, if flagIndir is set, pointer to data.
	// Valid when either flagIndir is set or typ.pointers() is true.
	// Gccgo always uses this field.
	ptr unsafe.Pointer

	// Non-pointer-valued data.  When the data is smaller
	// than a word, it begins at the first byte (in the memory
	// address sense) of this field.
	// Valid when flagIndir is not set and typ.pointers() is false.
	// Gccgo never uses this field.
	// scalar uintptr

	// flag holds metadata about the value.
	// The lowest bits are flag bits:
	//	- flagRO: obtained via unexported field, so read-only
	//	- flagIndir: val holds a pointer to the data
	//	- flagAddr: v.CanAddr is true (implies flagIndir)
	//	- flagMethod: v is a method value.
	// The next five bits give the Kind of the value.
	// This repeats typ.Kind() except for method values.
	// The remaining 23+ bits give a method number for method values.
	// If flag.kind() != Func, code can assume that flagMethod is unset.
	// If typ.size > ptrSize, code can assume that flagIndir is set.
	flag

	// A method value represents a curried method invocation
	// like r.Read for some receiver r.  The typ+val+flag bits describe
	// the receiver r, but the flag's Kind bits say Func (methods are
	// functions), and the top bits of the flag give the method number
	// in r's type's method table.
}

type flag uintptr

const (
	flagRO flag = 1 << iota
	flagIndir
	flagAddr
	flagMethod
	flagMethodFn         // gccgo: first fn parameter is always pointer
	flagKindShift        = iota
	flagKindWidth        = 5 // there are 27 kinds
	flagKindMask    flag = 1<<flagKindWidth - 1
	flagMethodShift      = flagKindShift + flagKindWidth
)

func (f flag) kind() Kind {
	return Kind((f >> flagKindShift) & flagKindMask)
}

// pointer returns the underlying pointer represented by v.
// v.Kind() must be Ptr, Map, Chan, Func, or UnsafePointer
func (v Value) pointer() unsafe.Pointer {
	if v.typ.size != ptrSize || !v.typ.pointers() {
		panic("can't call pointer on a non-pointer Value")
	}
	if v.flag&flagIndir != 0 {
		return *(*unsafe.Pointer)(v.ptr)
	}
	return v.ptr
}

// packEface converts v to the empty interface.
func packEface(v Value) interface{} {
	t := v.typ
	var i interface{}
	e := (*emptyInterface)(unsafe.Pointer(&i))
	// First, fill in the data portion of the interface.
	switch {
	case v.Kind() != Ptr && v.Kind() != UnsafePointer:
		// Value is indirect, and so is the interface we're making.
		if v.flag&flagIndir == 0 {
			panic("reflect: missing flagIndir")
		}
		ptr := v.ptr
		if v.flag&flagAddr != 0 {
			// TODO: pass safe boolean from valueInterface so
			// we don't need to copy if safe==true?
			c := unsafe_New(t)
			memmove(c, ptr, t.size)
			ptr = c
		}
		e.word = iword(ptr)
	case v.flag&flagIndir != 0:
		// Value is indirect, but interface is direct.  We need
		// to load the data at v.ptr into the interface data word.
		if t.pointers() {
			e.word = iword(*(*unsafe.Pointer)(v.ptr))
		} else {
			e.word = iword(loadScalar(v.ptr, t.size))
		}
	default:
		// Value is direct, and so is the interface.
		if t.pointers() {
			e.word = iword(v.ptr)
		} else {
			// e.word = iword(v.scalar)
			panic("reflect: missing flagIndir")
		}
	}
	// Now, fill in the type portion.  We're very careful here not
	// to have any operation between the e.word and e.typ assignments
	// that would let the garbage collector observe the partially-built
	// interface value.
	e.typ = t
	return i
}

// unpackEface converts the empty interface i to a Value.
func unpackEface(i interface{}) Value {
	e := (*emptyInterface)(unsafe.Pointer(&i))
	// NOTE: don't read e.word until we know whether it is really a pointer or not.
	t := e.typ
	if t == nil {
		return Value{}
	}
	f := flag(t.Kind()) << flagKindShift
	if t.Kind() != Ptr && t.Kind() != UnsafePointer {
		f |= flagIndir
	}
	return Value{t, unsafe.Pointer(e.word), f}
}

// A ValueError occurs when a Value method is invoked on
// a Value that does not support it.  Such cases are documented
// in the description of each method.
type ValueError struct {
	Method string
	Kind   Kind
}

func (e *ValueError) Error() string {
	if e.Kind == 0 {
		return "reflect: call of " + e.Method + " on zero Value"
	}
	return "reflect: call of " + e.Method + " on " + e.Kind.String() + " Value"
}

// methodName returns the name of the calling method,
// assumed to be two stack frames above.
func methodName() string {
	pc, _, _, _ := runtime.Caller(2)
	f := runtime.FuncForPC(pc)
	if f == nil {
		return "unknown method"
	}
	return f.Name()
}

// An iword is the word that would be stored in an
// interface to represent a given value v.  Specifically, if v is
// bigger than a pointer, its word is a pointer to v's data.
// Otherwise, its word holds the data stored
// in its leading bytes (so is not a pointer).
// This type is very dangerous for the garbage collector because
// it must be treated conservatively.  We try to never expose it
// to the GC here so that GC remains precise.
type iword unsafe.Pointer

// loadScalar loads n bytes at p from memory into a uintptr
// that forms the second word of an interface.  The data
// must be non-pointer in nature.
func loadScalar(p unsafe.Pointer, n uintptr) uintptr {
	// Run the copy ourselves instead of calling memmove
	// to avoid moving w to the heap.
	var w uintptr
	switch n {
	default:
		panic("reflect: internal error: loadScalar of " + strconv.Itoa(int(n)) + "-byte value")
	case 0:
	case 1:
		*(*uint8)(unsafe.Pointer(&w)) = *(*uint8)(p)
	case 2:
		*(*uint16)(unsafe.Pointer(&w)) = *(*uint16)(p)
	case 3:
		*(*[3]byte)(unsafe.Pointer(&w)) = *(*[3]byte)(p)
	case 4:
		*(*uint32)(unsafe.Pointer(&w)) = *(*uint32)(p)
	case 5:
		*(*[5]byte)(unsafe.Pointer(&w)) = *(*[5]byte)(p)
	case 6:
		*(*[6]byte)(unsafe.Pointer(&w)) = *(*[6]byte)(p)
	case 7:
		*(*[7]byte)(unsafe.Pointer(&w)) = *(*[7]byte)(p)
	case 8:
		*(*uint64)(unsafe.Pointer(&w)) = *(*uint64)(p)
	}
	return w
}

// storeScalar stores n bytes from w into p.
func storeScalar(p unsafe.Pointer, w uintptr, n uintptr) {
	// Run the copy ourselves instead of calling memmove
	// to avoid moving w to the heap.
	switch n {
	default:
		panic("reflect: internal error: storeScalar of " + strconv.Itoa(int(n)) + "-byte value")
	case 0:
	case 1:
		*(*uint8)(p) = *(*uint8)(unsafe.Pointer(&w))
	case 2:
		*(*uint16)(p) = *(*uint16)(unsafe.Pointer(&w))
	case 3:
		*(*[3]byte)(p) = *(*[3]byte)(unsafe.Pointer(&w))
	case 4:
		*(*uint32)(p) = *(*uint32)(unsafe.Pointer(&w))
	case 5:
		*(*[5]byte)(p) = *(*[5]byte)(unsafe.Pointer(&w))
	case 6:
		*(*[6]byte)(p) = *(*[6]byte)(unsafe.Pointer(&w))
	case 7:
		*(*[7]byte)(p) = *(*[7]byte)(unsafe.Pointer(&w))
	case 8:
		*(*uint64)(p) = *(*uint64)(unsafe.Pointer(&w))
	}
}

// emptyInterface is the header for an interface{} value.
type emptyInterface struct {
	typ  *rtype
	word iword
}

// nonEmptyInterface is the header for a interface value with methods.
type nonEmptyInterface struct {
	// see ../runtime/iface.c:/Itab
	itab *struct {
		typ *rtype                 // dynamic concrete type
		fun [100000]unsafe.Pointer // method table
	}
	word iword
}

// mustBe panics if f's kind is not expected.
// Making this a method on flag instead of on Value
// (and embedding flag in Value) means that we can write
// the very clear v.mustBe(Bool) and have it compile into
// v.flag.mustBe(Bool), which will only bother to copy the
// single important word for the receiver.
func (f flag) mustBe(expected Kind) {
	k := f.kind()
	if k != expected {
		panic(&ValueError{methodName(), k})
	}
}

// mustBeExported panics if f records that the value was obtained using
// an unexported field.
func (f flag) mustBeExported() {
	if f == 0 {
		panic(&ValueError{methodName(), 0})
	}
	if f&flagRO != 0 {
		panic("reflect: " + methodName() + " using value obtained using unexported field")
	}
}

// mustBeAssignable panics if f records that the value is not assignable,
// which is to say that either it was obtained using an unexported field
// or it is not addressable.
func (f flag) mustBeAssignable() {
	if f == 0 {
		panic(&ValueError{methodName(), Invalid})
	}
	// Assignable if addressable and not read-only.
	if f&flagRO != 0 {
		panic("reflect: " + methodName() + " using value obtained using unexported field")
	}
	if f&flagAddr == 0 {
		panic("reflect: " + methodName() + " using unaddressable value")
	}
}

// Addr returns a pointer value representing the address of v.
// It panics if CanAddr() returns false.
// Addr is typically used to obtain a pointer to a struct field
// or slice element in order to call a method that requires a
// pointer receiver.
func (v Value) Addr() Value {
	if v.flag&flagAddr == 0 {
		panic("reflect.Value.Addr of unaddressable value")
	}
	return Value{v.typ.ptrTo(), v.ptr /* 0, */, (v.flag & flagRO) | flag(Ptr)<<flagKindShift}
}

// Bool returns v's underlying value.
// It panics if v's kind is not Bool.
func (v Value) Bool() bool {
	v.mustBe(Bool)
	if v.flag&flagIndir != 0 {
		return *(*bool)(v.ptr)
	}
	// return *(*bool)(unsafe.Pointer(&v.scalar))
	panic("reflect: missing flagIndir")
}

// Bytes returns v's underlying value.
// It panics if v's underlying value is not a slice of bytes.
func (v Value) Bytes() []byte {
	v.mustBe(Slice)
	if v.typ.Elem().Kind() != Uint8 {
		panic("reflect.Value.Bytes of non-byte slice")
	}
	// Slice is always bigger than a word; assume flagIndir.
	return *(*[]byte)(v.ptr)
}

// runes returns v's underlying value.
// It panics if v's underlying value is not a slice of runes (int32s).
func (v Value) runes() []rune {
	v.mustBe(Slice)
	if v.typ.Elem().Kind() != Int32 {
		panic("reflect.Value.Bytes of non-rune slice")
	}
	// Slice is always bigger than a word; assume flagIndir.
	return *(*[]rune)(v.ptr)
}

// CanAddr returns true if the value's address can be obtained with Addr.
// Such values are called addressable.  A value is addressable if it is
// an element of a slice, an element of an addressable array,
// a field of an addressable struct, or the result of dereferencing a pointer.
// If CanAddr returns false, calling Addr will panic.
func (v Value) CanAddr() bool {
	return v.flag&flagAddr != 0
}

// CanSet returns true if the value of v can be changed.
// A Value can be changed only if it is addressable and was not
// obtained by the use of unexported struct fields.
// If CanSet returns false, calling Set or any type-specific
// setter (e.g., SetBool, SetInt64) will panic.
func (v Value) CanSet() bool {
	return v.flag&(flagAddr|flagRO) == flagAddr
}

// Call calls the function v with the input arguments in.
// For example, if len(in) == 3, v.Call(in) represents the Go call v(in[0], in[1], in[2]).
// Call panics if v's Kind is not Func.
// It returns the output results as Values.
// As in Go, each input argument must be assignable to the
// type of the function's corresponding input parameter.
// If v is a variadic function, Call creates the variadic slice parameter
// itself, copying in the corresponding values.
func (v Value) Call(in []Value) []Value {
	v.mustBe(Func)
	v.mustBeExported()
	return v.call("Call", in)
}

// CallSlice calls the variadic function v with the input arguments in,
// assigning the slice in[len(in)-1] to v's final variadic argument.
// For example, if len(in) == 3, v.Call(in) represents the Go call v(in[0], in[1], in[2]...).
// Call panics if v's Kind is not Func or if v is not variadic.
// It returns the output results as Values.
// As in Go, each input argument must be assignable to the
// type of the function's corresponding input parameter.
func (v Value) CallSlice(in []Value) []Value {
	v.mustBe(Func)
	v.mustBeExported()
	return v.call("CallSlice", in)
}

var callGC bool // for testing; see TestCallMethodJump

var makeFuncStubFn = makeFuncStub
var makeFuncStubCode = **(**uintptr)(unsafe.Pointer(&makeFuncStubFn))

func (v Value) call(op string, in []Value) []Value {
	// Get function pointer, type.
	t := v.typ
	var (
		fn   unsafe.Pointer
		rcvr Value
	)
	if v.flag&flagMethod != 0 {
		rcvr = v
		_, t, fn = methodReceiver(op, v, int(v.flag)>>flagMethodShift)
	} else if v.flag&flagIndir != 0 {
		fn = *(*unsafe.Pointer)(v.ptr)
	} else {
		fn = v.ptr
	}

	if fn == nil {
		panic("reflect.Value.Call: call of nil function")
	}

	isSlice := op == "CallSlice"
	n := t.NumIn()
	if isSlice {
		if !t.IsVariadic() {
			panic("reflect: CallSlice of non-variadic function")
		}
		if len(in) < n {
			panic("reflect: CallSlice with too few input arguments")
		}
		if len(in) > n {
			panic("reflect: CallSlice with too many input arguments")
		}
	} else {
		if t.IsVariadic() {
			n--
		}
		if len(in) < n {
			panic("reflect: Call with too few input arguments")
		}
		if !t.IsVariadic() && len(in) > n {
			panic("reflect: Call with too many input arguments")
		}
	}
	for _, x := range in {
		if x.Kind() == Invalid {
			panic("reflect: " + op + " using zero Value argument")
		}
	}
	for i := 0; i < n; i++ {
		if xt, targ := in[i].Type(), t.In(i); !xt.AssignableTo(targ) {
			panic("reflect: " + op + " using " + xt.String() + " as type " + targ.String())
		}
	}
	if !isSlice && t.IsVariadic() {
		// prepare slice for remaining values
		m := len(in) - n
		slice := MakeSlice(t.In(n), m, m)
		elem := t.In(n).Elem()
		for i := 0; i < m; i++ {
			x := in[n+i]
			if xt := x.Type(); !xt.AssignableTo(elem) {
				panic("reflect: cannot use " + xt.String() + " as type " + elem.String() + " in " + op)
			}
			slice.Index(i).Set(x)
		}
		origIn := in
		in = make([]Value, n+1)
		copy(in[:n], origIn)
		in[n] = slice
	}

	nin := len(in)
	if nin != t.NumIn() {
		panic("reflect.Value.Call: wrong argument count")
	}
	nout := t.NumOut()

	// If target is makeFuncStub, short circuit the unpack onto stack /
	// pack back into []Value for the args and return values.  Just do the
	// call directly.
	// We need to do this here because otherwise we have a situation where
	// reflect.callXX calls makeFuncStub, neither of which knows the
	// layout of the args.  That's bad for precise gc & stack copying.
	x := (*makeFuncImpl)(fn)
	if x.code == makeFuncStubCode {
		return x.call(in)
	}

	if v.flag&flagMethod != 0 {
		nin++
	}
	firstPointer := len(in) > 0 && t.In(0).Kind() != Ptr && v.flag&flagMethodFn != 0
	params := make([]unsafe.Pointer, nin)
	off := 0
	if v.flag&flagMethod != 0 {
		// Hard-wired first argument.
		p := new(unsafe.Pointer)
		if rcvr.typ.Kind() == Interface {
			*p = unsafe.Pointer((*nonEmptyInterface)(v.ptr).word)
		} else if rcvr.typ.Kind() == Ptr || rcvr.typ.Kind() == UnsafePointer {
			*p = rcvr.pointer()
		} else {
			*p = rcvr.ptr
		}
		params[0] = unsafe.Pointer(p)
		off = 1
	}
	for i, pv := range in {
		pv.mustBeExported()
		targ := t.In(i).(*rtype)
		pv = pv.assignTo("reflect.Value.Call", targ, nil)
		if pv.flag&flagIndir == 0 {
			p := new(unsafe.Pointer)
			*p = pv.ptr
			params[off] = unsafe.Pointer(p)
		} else {
			params[off] = pv.ptr
		}
		if i == 0 && firstPointer {
			p := new(unsafe.Pointer)
			*p = params[off]
			params[off] = unsafe.Pointer(p)
		}
		off++
	}

	ret := make([]Value, nout)
	results := make([]unsafe.Pointer, nout)
	for i := 0; i < nout; i++ {
		v := New(t.Out(i))
		results[i] = unsafe.Pointer(v.Pointer())
		ret[i] = Indirect(v)
	}

	var pp *unsafe.Pointer
	if len(params) > 0 {
		pp = &params[0]
	}
	var pr *unsafe.Pointer
	if len(results) > 0 {
		pr = &results[0]
	}

	call(t, fn, v.flag&flagMethod != 0, firstPointer, pp, pr)

	// For testing; see TestCallMethodJump.
	if callGC {
		runtime.GC()
	}

	return ret
}

// methodReceiver returns information about the receiver
// described by v. The Value v may or may not have the
// flagMethod bit set, so the kind cached in v.flag should
// not be used.
// The return value rcvrtype gives the method's actual receiver type.
// The return value t gives the method type signature (without the receiver).
// The return value fn is a pointer to the method code.
func methodReceiver(op string, v Value, methodIndex int) (rcvrtype, t *rtype, fn unsafe.Pointer) {
	i := methodIndex
	if v.typ.Kind() == Interface {
		tt := (*interfaceType)(unsafe.Pointer(v.typ))
		if i < 0 || i >= len(tt.methods) {
			panic("reflect: internal error: invalid method index")
		}
		m := &tt.methods[i]
		if m.pkgPath != nil {
			panic("reflect: " + op + " of unexported method")
		}
		iface := (*nonEmptyInterface)(v.ptr)
		if iface.itab == nil {
			panic("reflect: " + op + " of method on nil interface value")
		}
		rcvrtype = iface.itab.typ
		fn = unsafe.Pointer(&iface.itab.fun[i])
		t = m.typ
	} else {
		rcvrtype = v.typ
		ut := v.typ.uncommon()
		if ut == nil || i < 0 || i >= len(ut.methods) {
			panic("reflect: internal error: invalid method index")
		}
		m := &ut.methods[i]
		if m.pkgPath != nil {
			panic("reflect: " + op + " of unexported method")
		}
		fn = unsafe.Pointer(&m.tfn)
		t = m.mtyp
	}
	return
}

// v is a method receiver.  Store at p the word which is used to
// encode that receiver at the start of the argument list.
// Reflect uses the "interface" calling convention for
// methods, which always uses one word to record the receiver.
func storeRcvr(v Value, p unsafe.Pointer) {
	t := v.typ
	if t.Kind() == Interface {
		// the interface data word becomes the receiver word
		iface := (*nonEmptyInterface)(v.ptr)
		*(*unsafe.Pointer)(p) = unsafe.Pointer(iface.word)
	} else if v.flag&flagIndir != 0 {
		if t.size > ptrSize {
			*(*unsafe.Pointer)(p) = v.ptr
		} else if t.pointers() {
			*(*unsafe.Pointer)(p) = *(*unsafe.Pointer)(v.ptr)
		} else {
			*(*uintptr)(p) = loadScalar(v.ptr, t.size)
		}
	} else if t.pointers() {
		*(*unsafe.Pointer)(p) = v.ptr
	} else {
		// *(*uintptr)(p) = v.scalar
		panic("reflect: missing flagIndir")
	}
}

// align returns the result of rounding x up to a multiple of n.
// n must be a power of two.
func align(x, n uintptr) uintptr {
	return (x + n - 1) &^ (n - 1)
}

// funcName returns the name of f, for use in error messages.
func funcName(f func([]Value) []Value) string {
	pc := *(*uintptr)(unsafe.Pointer(&f))
	rf := runtime.FuncForPC(pc)
	if rf != nil {
		return rf.Name()
	}
	return "closure"
}

// Cap returns v's capacity.
// It panics if v's Kind is not Array, Chan, or Slice.
func (v Value) Cap() int {
	k := v.kind()
	switch k {
	case Array:
		return v.typ.Len()
	case Chan:
		return int(chancap(v.pointer()))
	case Slice:
		// Slice is always bigger than a word; assume flagIndir.
		return (*sliceHeader)(v.ptr).Cap
	}
	panic(&ValueError{"reflect.Value.Cap", k})
}

// Close closes the channel v.
// It panics if v's Kind is not Chan.
func (v Value) Close() {
	v.mustBe(Chan)
	v.mustBeExported()
	chanclose(v.pointer())
}

// Complex returns v's underlying value, as a complex128.
// It panics if v's Kind is not Complex64 or Complex128
func (v Value) Complex() complex128 {
	k := v.kind()
	switch k {
	case Complex64:
		if v.flag&flagIndir != 0 {
			return complex128(*(*complex64)(v.ptr))
		}
		// return complex128(*(*complex64)(unsafe.Pointer(&v.scalar)))
		panic("reflect: missing flagIndir")
	case Complex128:
		// complex128 is always bigger than a word; assume flagIndir.
		return *(*complex128)(v.ptr)
	}
	panic(&ValueError{"reflect.Value.Complex", k})
}

// Elem returns the value that the interface v contains
// or that the pointer v points to.
// It panics if v's Kind is not Interface or Ptr.
// It returns the zero Value if v is nil.
func (v Value) Elem() Value {
	k := v.kind()
	switch k {
	case Interface:
		var eface interface{}
		if v.typ.NumMethod() == 0 {
			eface = *(*interface{})(v.ptr)
		} else {
			eface = (interface{})(*(*interface {
				M()
			})(v.ptr))
		}
		x := unpackEface(eface)
		x.flag |= v.flag & flagRO
		return x
	case Ptr:
		ptr := v.ptr
		if v.flag&flagIndir != 0 {
			ptr = *(*unsafe.Pointer)(ptr)
		}
		// The returned value's address is v's value.
		if ptr == nil {
			return Value{}
		}
		tt := (*ptrType)(unsafe.Pointer(v.typ))
		typ := tt.elem
		fl := v.flag&flagRO | flagIndir | flagAddr
		fl |= flag(typ.Kind() << flagKindShift)
		return Value{typ, ptr /* 0, */, fl}
	}
	panic(&ValueError{"reflect.Value.Elem", k})
}

// Field returns the i'th field of the struct v.
// It panics if v's Kind is not Struct or i is out of range.
func (v Value) Field(i int) Value {
	v.mustBe(Struct)
	tt := (*structType)(unsafe.Pointer(v.typ))
	if i < 0 || i >= len(tt.fields) {
		panic("reflect: Field index out of range")
	}
	field := &tt.fields[i]
	typ := field.typ

	// Inherit permission bits from v.
	fl := v.flag & (flagRO | flagIndir | flagAddr)
	// Using an unexported field forces flagRO.
	if field.pkgPath != nil {
		fl |= flagRO
	}
	fl |= flag(typ.Kind()) << flagKindShift

	var ptr unsafe.Pointer
	// var scalar uintptr
	switch {
	case fl&flagIndir != 0:
		// Indirect.  Just bump pointer.
		ptr = unsafe.Pointer(uintptr(v.ptr) + field.offset)
	case typ.pointers():
		if field.offset != 0 {
			panic("field access of ptr value isn't at offset 0")
		}
		ptr = v.ptr
	case bigEndian:
		// Must be scalar.  Discard leading bytes.
		// scalar = v.scalar << (field.offset * 8)
		panic("reflect: missing flagIndir")
	default:
		// Must be scalar.  Discard leading bytes.
		// scalar = v.scalar >> (field.offset * 8)
		panic("reflect: missing flagIndir")
	}

	return Value{typ, ptr /* scalar, */, fl}
}

// FieldByIndex returns the nested field corresponding to index.
// It panics if v's Kind is not struct.
func (v Value) FieldByIndex(index []int) Value {
	v.mustBe(Struct)
	for i, x := range index {
		if i > 0 {
			if v.Kind() == Ptr && v.typ.Elem().Kind() == Struct {
				if v.IsNil() {
					panic("reflect: indirection through nil pointer to embedded struct")
				}
				v = v.Elem()
			}
		}
		v = v.Field(x)
	}
	return v
}

// FieldByName returns the struct field with the given name.
// It returns the zero Value if no field was found.
// It panics if v's Kind is not struct.
func (v Value) FieldByName(name string) Value {
	v.mustBe(Struct)
	if f, ok := v.typ.FieldByName(name); ok {
		return v.FieldByIndex(f.Index)
	}
	return Value{}
}

// FieldByNameFunc returns the struct field with a name
// that satisfies the match function.
// It panics if v's Kind is not struct.
// It returns the zero Value if no field was found.
func (v Value) FieldByNameFunc(match func(string) bool) Value {
	v.mustBe(Struct)
	if f, ok := v.typ.FieldByNameFunc(match); ok {
		return v.FieldByIndex(f.Index)
	}
	return Value{}
}

// Float returns v's underlying value, as a float64.
// It panics if v's Kind is not Float32 or Float64
func (v Value) Float() float64 {
	k := v.kind()
	switch k {
	case Float32:
		if v.flag&flagIndir != 0 {
			return float64(*(*float32)(v.ptr))
		}
		// return float64(*(*float32)(unsafe.Pointer(&v.scalar)))
		panic("reflect: missing flagIndir")
	case Float64:
		if v.flag&flagIndir != 0 {
			return *(*float64)(v.ptr)
		}
		// return *(*float64)(unsafe.Pointer(&v.scalar))
		panic("reflect: missing flagIndir")
	}
	panic(&ValueError{"reflect.Value.Float", k})
}

var uint8Type = TypeOf(uint8(0)).(*rtype)

// Index returns v's i'th element.
// It panics if v's Kind is not Array, Slice, or String or i is out of range.
func (v Value) Index(i int) Value {
	k := v.kind()
	switch k {
	case Array:
		tt := (*arrayType)(unsafe.Pointer(v.typ))
		if i < 0 || i > int(tt.len) {
			panic("reflect: array index out of range")
		}
		typ := tt.elem
		fl := v.flag & (flagRO | flagIndir | flagAddr) // bits same as overall array
		fl |= flag(typ.Kind()) << flagKindShift
		offset := uintptr(i) * typ.size

		var val unsafe.Pointer
		switch {
		case fl&flagIndir != 0:
			// Indirect.  Just bump pointer.
			val = unsafe.Pointer(uintptr(v.ptr) + offset)
		case typ.pointers():
			if offset != 0 {
				panic("can't Index(i) with i!=0 on ptrLike value")
			}
			val = v.ptr
		case bigEndian:
			// Direct.  Discard leading bytes.
			// scalar = v.scalar << (offset * 8)
			panic("reflect: missing flagIndir")
		default:
			// Direct.  Discard leading bytes.
			// scalar = v.scalar >> (offset * 8)
			panic("reflect: missing flagIndir")
		}
		return Value{typ, val /* scalar, */, fl}

	case Slice:
		// Element flag same as Elem of Ptr.
		// Addressable, indirect, possibly read-only.
		fl := flagAddr | flagIndir | v.flag&flagRO
		s := (*sliceHeader)(v.ptr)
		if i < 0 || i >= s.Len {
			panic("reflect: slice index out of range")
		}
		tt := (*sliceType)(unsafe.Pointer(v.typ))
		typ := tt.elem
		fl |= flag(typ.Kind()) << flagKindShift
		val := unsafe.Pointer(uintptr(s.Data) + uintptr(i)*typ.size)
		return Value{typ, val /* 0, */, fl}

	case String:
		fl := v.flag&flagRO | flag(Uint8<<flagKindShift) | flagIndir
		s := (*StringHeader)(v.ptr)
		if i < 0 || i >= s.Len {
			panic("reflect: string index out of range")
		}
		b := uintptr(0)
		*(*byte)(unsafe.Pointer(&b)) = *(*byte)(unsafe.Pointer(uintptr(s.Data) + uintptr(i)))
		return Value{uint8Type, unsafe.Pointer(&b) /* 0, */, fl | flagIndir}
	}
	panic(&ValueError{"reflect.Value.Index", k})
}

// Int returns v's underlying value, as an int64.
// It panics if v's Kind is not Int, Int8, Int16, Int32, or Int64.
func (v Value) Int() int64 {
	k := v.kind()
	var p unsafe.Pointer
	if v.flag&flagIndir != 0 {
		p = v.ptr
	} else {
		// The escape analysis is good enough that &v.scalar
		// does not trigger a heap allocation.
		// p = unsafe.Pointer(&v.scalar)
		switch k {
		case Int, Int8, Int16, Int32, Int64:
			panic("reflect: missing flagIndir")
		}
	}
	switch k {
	case Int:
		return int64(*(*int)(p))
	case Int8:
		return int64(*(*int8)(p))
	case Int16:
		return int64(*(*int16)(p))
	case Int32:
		return int64(*(*int32)(p))
	case Int64:
		return int64(*(*int64)(p))
	}
	panic(&ValueError{"reflect.Value.Int", k})
}

// CanInterface returns true if Interface can be used without panicking.
func (v Value) CanInterface() bool {
	if v.flag == 0 {
		panic(&ValueError{"reflect.Value.CanInterface", Invalid})
	}
	return v.flag&flagRO == 0
}

// Interface returns v's current value as an interface{}.
// It is equivalent to:
//	var i interface{} = (v's underlying value)
// It panics if the Value was obtained by accessing
// unexported struct fields.
func (v Value) Interface() (i interface{}) {
	return valueInterface(v, true)
}

func valueInterface(v Value, safe bool) interface{} {
	if v.flag == 0 {
		panic(&ValueError{"reflect.Value.Interface", 0})
	}
	if safe && v.flag&flagRO != 0 {
		// Do not allow access to unexported values via Interface,
		// because they might be pointers that should not be
		// writable or methods or function that should not be callable.
		panic("reflect.Value.Interface: cannot return value obtained from unexported field or method")
	}
	if v.flag&flagMethod != 0 {
		v = makeMethodValue("Interface", v)
	}

	if v.flag&flagMethodFn != 0 {
		if v.typ.Kind() != Func {
			panic("reflect: MethodFn of non-Func")
		}
		ft := (*funcType)(unsafe.Pointer(v.typ))
		if ft.in[0].Kind() != Ptr {
			v = makeValueMethod(v)
		}
	}

	if v.kind() == Interface {
		// Special case: return the element inside the interface.
		// Empty interface has one layout, all interfaces with
		// methods have a second layout.
		if v.NumMethod() == 0 {
			return *(*interface{})(v.ptr)
		}
		return *(*interface {
			M()
		})(v.ptr)
	}

	// TODO: pass safe to packEface so we don't need to copy if safe==true?
	return packEface(v)
}

// InterfaceData returns the interface v's value as a uintptr pair.
// It panics if v's Kind is not Interface.
func (v Value) InterfaceData() [2]uintptr {
	// TODO: deprecate this
	v.mustBe(Interface)
	// We treat this as a read operation, so we allow
	// it even for unexported data, because the caller
	// has to import "unsafe" to turn it into something
	// that can be abused.
	// Interface value is always bigger than a word; assume flagIndir.
	return *(*[2]uintptr)(v.ptr)
}

// IsNil reports whether its argument v is nil. The argument must be
// a chan, func, interface, map, pointer, or slice value; if it is
// not, IsNil panics. Note that IsNil is not always equivalent to a
// regular comparison with nil in Go. For example, if v was created
// by calling ValueOf with an uninitialized interface variable i,
// i==nil will be true but v.IsNil will panic as v will be the zero
// Value.
func (v Value) IsNil() bool {
	k := v.kind()
	switch k {
	case Chan, Func, Map, Ptr:
		if v.flag&flagMethod != 0 {
			return false
		}
		ptr := v.ptr
		if v.flag&flagIndir != 0 {
			ptr = *(*unsafe.Pointer)(ptr)
		}
		return ptr == nil
	case Interface, Slice:
		// Both interface and slice are nil if first word is 0.
		// Both are always bigger than a word; assume flagIndir.
		return *(*unsafe.Pointer)(v.ptr) == nil
	}
	panic(&ValueError{"reflect.Value.IsNil", k})
}

// IsValid returns true if v represents a value.
// It returns false if v is the zero Value.
// If IsValid returns false, all other methods except String panic.
// Most functions and methods never return an invalid value.
// If one does, its documentation states the conditions explicitly.
func (v Value) IsValid() bool {
	return v.flag != 0
}

// Kind returns v's Kind.
// If v is the zero Value (IsValid returns false), Kind returns Invalid.
func (v Value) Kind() Kind {
	return v.kind()
}

// Len returns v's length.
// It panics if v's Kind is not Array, Chan, Map, Slice, or String.
func (v Value) Len() int {
	k := v.kind()
	switch k {
	case Array:
		tt := (*arrayType)(unsafe.Pointer(v.typ))
		return int(tt.len)
	case Chan:
		return chanlen(v.pointer())
	case Map:
		return maplen(v.pointer())
	case Slice:
		// Slice is bigger than a word; assume flagIndir.
		return (*sliceHeader)(v.ptr).Len
	case String:
		// String is bigger than a word; assume flagIndir.
		return (*stringHeader)(v.ptr).Len
	}
	panic(&ValueError{"reflect.Value.Len", k})
}

// MapIndex returns the value associated with key in the map v.
// It panics if v's Kind is not Map.
// It returns the zero Value if key is not found in the map or if v represents a nil map.
// As in Go, the key's value must be assignable to the map's key type.
func (v Value) MapIndex(key Value) Value {
	v.mustBe(Map)
	tt := (*mapType)(unsafe.Pointer(v.typ))

	// Do not require key to be exported, so that DeepEqual
	// and other programs can use all the keys returned by
	// MapKeys as arguments to MapIndex.  If either the map
	// or the key is unexported, though, the result will be
	// considered unexported.  This is consistent with the
	// behavior for structs, which allow read but not write
	// of unexported fields.
	key = key.assignTo("reflect.Value.MapIndex", tt.key, nil)

	var k unsafe.Pointer
	if key.flag&flagIndir != 0 {
		k = key.ptr
	} else if key.typ.pointers() {
		k = unsafe.Pointer(&key.ptr)
	} else {
		// k = unsafe.Pointer(&key.scalar)
		panic("reflect: missing flagIndir")
	}
	e := mapaccess(v.typ, v.pointer(), k)
	if e == nil {
		return Value{}
	}
	typ := tt.elem
	fl := (v.flag | key.flag) & flagRO
	fl |= flag(typ.Kind()) << flagKindShift
	if typ.Kind() != Ptr && typ.Kind() != UnsafePointer {
		// Copy result so future changes to the map
		// won't change the underlying value.
		c := unsafe_New(typ)
		memmove(c, e, typ.size)
		return Value{typ, c /* 0, */, fl | flagIndir}
	} else if typ.pointers() {
		return Value{typ, *(*unsafe.Pointer)(e) /* 0, */, fl}
	} else {
		panic("reflect: can't happen")
	}
}

// MapKeys returns a slice containing all the keys present in the map,
// in unspecified order.
// It panics if v's Kind is not Map.
// It returns an empty slice if v represents a nil map.
func (v Value) MapKeys() []Value {
	v.mustBe(Map)
	tt := (*mapType)(unsafe.Pointer(v.typ))
	keyType := tt.key

	fl := v.flag&flagRO | flag(keyType.Kind())<<flagKindShift
	if keyType.Kind() != Ptr && keyType.Kind() != UnsafePointer {
		fl |= flagIndir
	}

	m := v.pointer()
	mlen := int(0)
	if m != nil {
		mlen = maplen(m)
	}
	it := mapiterinit(v.typ, m)
	a := make([]Value, mlen)
	var i int
	for i = 0; i < len(a); i++ {
		key := mapiterkey(it)
		if key == nil {
			// Someone deleted an entry from the map since we
			// called maplen above.  It's a data race, but nothing
			// we can do about it.
			break
		}
		if keyType.Kind() != Ptr && keyType.Kind() != UnsafePointer {
			// Copy result so future changes to the map
			// won't change the underlying value.
			c := unsafe_New(keyType)
			memmove(c, key, keyType.size)
			a[i] = Value{keyType, c /* 0, */, fl | flagIndir}
		} else if keyType.pointers() {
			a[i] = Value{keyType, *(*unsafe.Pointer)(key) /* 0, */, fl}
		} else {
			panic("reflect: can't happen")
		}
		mapiternext(it)
	}
	return a[:i]
}

// Method returns a function value corresponding to v's i'th method.
// The arguments to a Call on the returned function should not include
// a receiver; the returned function will always use v as the receiver.
// Method panics if i is out of range or if v is a nil interface value.
func (v Value) Method(i int) Value {
	if v.typ == nil {
		panic(&ValueError{"reflect.Value.Method", Invalid})
	}
	if v.flag&flagMethod != 0 || i < 0 || i >= v.typ.NumMethod() {
		panic("reflect: Method index out of range")
	}
	if v.typ.Kind() == Interface && v.IsNil() {
		panic("reflect: Method on nil interface value")
	}
	fl := v.flag & (flagRO | flagIndir)
	fl |= flag(Func) << flagKindShift
	fl |= flag(i)<<flagMethodShift | flagMethod
	return Value{v.typ, v.ptr /* v.scalar, */, fl}
}

// NumMethod returns the number of methods in the value's method set.
func (v Value) NumMethod() int {
	if v.typ == nil {
		panic(&ValueError{"reflect.Value.NumMethod", Invalid})
	}
	if v.flag&flagMethod != 0 {
		return 0
	}
	return v.typ.NumMethod()
}

// MethodByName returns a function value corresponding to the method
// of v with the given name.
// The arguments to a Call on the returned function should not include
// a receiver; the returned function will always use v as the receiver.
// It returns the zero Value if no method was found.
func (v Value) MethodByName(name string) Value {
	if v.typ == nil {
		panic(&ValueError{"reflect.Value.MethodByName", Invalid})
	}
	if v.flag&flagMethod != 0 {
		return Value{}
	}
	m, ok := v.typ.MethodByName(name)
	if !ok {
		return Value{}
	}
	return v.Method(m.Index)
}

// NumField returns the number of fields in the struct v.
// It panics if v's Kind is not Struct.
func (v Value) NumField() int {
	v.mustBe(Struct)
	tt := (*structType)(unsafe.Pointer(v.typ))
	return len(tt.fields)
}

// OverflowComplex returns true if the complex128 x cannot be represented by v's type.
// It panics if v's Kind is not Complex64 or Complex128.
func (v Value) OverflowComplex(x complex128) bool {
	k := v.kind()
	switch k {
	case Complex64:
		return overflowFloat32(real(x)) || overflowFloat32(imag(x))
	case Complex128:
		return false
	}
	panic(&ValueError{"reflect.Value.OverflowComplex", k})
}

// OverflowFloat returns true if the float64 x cannot be represented by v's type.
// It panics if v's Kind is not Float32 or Float64.
func (v Value) OverflowFloat(x float64) bool {
	k := v.kind()
	switch k {
	case Float32:
		return overflowFloat32(x)
	case Float64:
		return false
	}
	panic(&ValueError{"reflect.Value.OverflowFloat", k})
}

func overflowFloat32(x float64) bool {
	if x < 0 {
		x = -x
	}
	return math.MaxFloat32 < x && x <= math.MaxFloat64
}

// OverflowInt returns true if the int64 x cannot be represented by v's type.
// It panics if v's Kind is not Int, Int8, int16, Int32, or Int64.
func (v Value) OverflowInt(x int64) bool {
	k := v.kind()
	switch k {
	case Int, Int8, Int16, Int32, Int64:
		bitSize := v.typ.size * 8
		trunc := (x << (64 - bitSize)) >> (64 - bitSize)
		return x != trunc
	}
	panic(&ValueError{"reflect.Value.OverflowInt", k})
}

// OverflowUint returns true if the uint64 x cannot be represented by v's type.
// It panics if v's Kind is not Uint, Uintptr, Uint8, Uint16, Uint32, or Uint64.
func (v Value) OverflowUint(x uint64) bool {
	k := v.kind()
	switch k {
	case Uint, Uintptr, Uint8, Uint16, Uint32, Uint64:
		bitSize := v.typ.size * 8
		trunc := (x << (64 - bitSize)) >> (64 - bitSize)
		return x != trunc
	}
	panic(&ValueError{"reflect.Value.OverflowUint", k})
}

// Pointer returns v's value as a uintptr.
// It returns uintptr instead of unsafe.Pointer so that
// code using reflect cannot obtain unsafe.Pointers
// without importing the unsafe package explicitly.
// It panics if v's Kind is not Chan, Func, Map, Ptr, Slice, or UnsafePointer.
//
// If v's Kind is Func, the returned pointer is an underlying
// code pointer, but not necessarily enough to identify a
// single function uniquely. The only guarantee is that the
// result is zero if and only if v is a nil func Value.
//
// If v's Kind is Slice, the returned pointer is to the first
// element of the slice.  If the slice is nil the returned value
// is 0.  If the slice is empty but non-nil the return value is non-zero.
func (v Value) Pointer() uintptr {
	// TODO: deprecate
	k := v.kind()
	switch k {
	case Chan, Map, Ptr, UnsafePointer:
		return uintptr(v.pointer())
	case Func:
		if v.flag&flagMethod != 0 {
			// As the doc comment says, the returned pointer is an
			// underlying code pointer but not necessarily enough to
			// identify a single function uniquely. All method expressions
			// created via reflect have the same underlying code pointer,
			// so their Pointers are equal. The function used here must
			// match the one used in makeMethodValue.
			f := makeFuncStub
			return **(**uintptr)(unsafe.Pointer(&f))
		}
		p := v.pointer()
		// Non-nil func value points at data block.
		// First word of data block is actual code.
		if p != nil {
			p = *(*unsafe.Pointer)(p)
		}
		return uintptr(p)

	case Slice:
		return (*SliceHeader)(v.ptr).Data
	}
	panic(&ValueError{"reflect.Value.Pointer", k})
}

// Recv receives and returns a value from the channel v.
// It panics if v's Kind is not Chan.
// The receive blocks until a value is ready.
// The boolean value ok is true if the value x corresponds to a send
// on the channel, false if it is a zero value received because the channel is closed.
func (v Value) Recv() (x Value, ok bool) {
	v.mustBe(Chan)
	v.mustBeExported()
	return v.recv(false)
}

// internal recv, possibly non-blocking (nb).
// v is known to be a channel.
func (v Value) recv(nb bool) (val Value, ok bool) {
	tt := (*chanType)(unsafe.Pointer(v.typ))
	if ChanDir(tt.dir)&RecvDir == 0 {
		panic("reflect: recv on send-only channel")
	}
	t := tt.elem
	val = Value{t, nil /* 0, */, flag(t.Kind()) << flagKindShift}
	var p unsafe.Pointer
	if t.Kind() != Ptr && t.Kind() != UnsafePointer {
		p = unsafe_New(t)
		val.ptr = p
		val.flag |= flagIndir
	} else {
		p = unsafe.Pointer(&val.ptr)
	}
	selected, ok := chanrecv(v.typ, v.pointer(), nb, p)
	if !selected {
		val = Value{}
	}
	return
}

// Send sends x on the channel v.
// It panics if v's kind is not Chan or if x's type is not the same type as v's element type.
// As in Go, x's value must be assignable to the channel's element type.
func (v Value) Send(x Value) {
	v.mustBe(Chan)
	v.mustBeExported()
	v.send(x, false)
}

// internal send, possibly non-blocking.
// v is known to be a channel.
func (v Value) send(x Value, nb bool) (selected bool) {
	tt := (*chanType)(unsafe.Pointer(v.typ))
	if ChanDir(tt.dir)&SendDir == 0 {
		panic("reflect: send on recv-only channel")
	}
	x.mustBeExported()
	x = x.assignTo("reflect.Value.Send", tt.elem, nil)
	var p unsafe.Pointer
	if x.flag&flagIndir != 0 {
		p = x.ptr
	} else if x.typ.pointers() {
		p = unsafe.Pointer(&x.ptr)
	} else {
		// p = unsafe.Pointer(&x.scalar)
		panic("reflect: missing flagIndir")
	}
	return chansend(v.typ, v.pointer(), p, nb)
}

// Set assigns x to the value v.
// It panics if CanSet returns false.
// As in Go, x's value must be assignable to v's type.
func (v Value) Set(x Value) {
	v.mustBeAssignable()
	x.mustBeExported() // do not let unexported x leak
	var target *interface{}
	if v.kind() == Interface {
		target = (*interface{})(v.ptr)
	}
	x = x.assignTo("reflect.Set", v.typ, target)
	if x.flag&flagIndir != 0 {
		memmove(v.ptr, x.ptr, v.typ.size)
	} else if x.typ.pointers() {
		*(*unsafe.Pointer)(v.ptr) = x.ptr
	} else {
		// memmove(v.ptr, unsafe.Pointer(&x.scalar), v.typ.size)
		panic("reflect: missing flagIndir")
	}
}

// SetBool sets v's underlying value.
// It panics if v's Kind is not Bool or if CanSet() is false.
func (v Value) SetBool(x bool) {
	v.mustBeAssignable()
	v.mustBe(Bool)
	*(*bool)(v.ptr) = x
}

// SetBytes sets v's underlying value.
// It panics if v's underlying value is not a slice of bytes.
func (v Value) SetBytes(x []byte) {
	v.mustBeAssignable()
	v.mustBe(Slice)
	if v.typ.Elem().Kind() != Uint8 {
		panic("reflect.Value.SetBytes of non-byte slice")
	}
	*(*[]byte)(v.ptr) = x
}

// setRunes sets v's underlying value.
// It panics if v's underlying value is not a slice of runes (int32s).
func (v Value) setRunes(x []rune) {
	v.mustBeAssignable()
	v.mustBe(Slice)
	if v.typ.Elem().Kind() != Int32 {
		panic("reflect.Value.setRunes of non-rune slice")
	}
	*(*[]rune)(v.ptr) = x
}

// SetComplex sets v's underlying value to x.
// It panics if v's Kind is not Complex64 or Complex128, or if CanSet() is false.
func (v Value) SetComplex(x complex128) {
	v.mustBeAssignable()
	switch k := v.kind(); k {
	default:
		panic(&ValueError{"reflect.Value.SetComplex", k})
	case Complex64:
		*(*complex64)(v.ptr) = complex64(x)
	case Complex128:
		*(*complex128)(v.ptr) = x
	}
}

// SetFloat sets v's underlying value to x.
// It panics if v's Kind is not Float32 or Float64, or if CanSet() is false.
func (v Value) SetFloat(x float64) {
	v.mustBeAssignable()
	switch k := v.kind(); k {
	default:
		panic(&ValueError{"reflect.Value.SetFloat", k})
	case Float32:
		*(*float32)(v.ptr) = float32(x)
	case Float64:
		*(*float64)(v.ptr) = x
	}
}

// SetInt sets v's underlying value to x.
// It panics if v's Kind is not Int, Int8, Int16, Int32, or Int64, or if CanSet() is false.
func (v Value) SetInt(x int64) {
	v.mustBeAssignable()
	switch k := v.kind(); k {
	default:
		panic(&ValueError{"reflect.Value.SetInt", k})
	case Int:
		*(*int)(v.ptr) = int(x)
	case Int8:
		*(*int8)(v.ptr) = int8(x)
	case Int16:
		*(*int16)(v.ptr) = int16(x)
	case Int32:
		*(*int32)(v.ptr) = int32(x)
	case Int64:
		*(*int64)(v.ptr) = x
	}
}

// SetLen sets v's length to n.
// It panics if v's Kind is not Slice or if n is negative or
// greater than the capacity of the slice.
func (v Value) SetLen(n int) {
	v.mustBeAssignable()
	v.mustBe(Slice)
	s := (*sliceHeader)(v.ptr)
	if n < 0 || n > int(s.Cap) {
		panic("reflect: slice length out of range in SetLen")
	}
	s.Len = n
}

// SetCap sets v's capacity to n.
// It panics if v's Kind is not Slice or if n is smaller than the length or
// greater than the capacity of the slice.
func (v Value) SetCap(n int) {
	v.mustBeAssignable()
	v.mustBe(Slice)
	s := (*sliceHeader)(v.ptr)
	if n < int(s.Len) || n > int(s.Cap) {
		panic("reflect: slice capacity out of range in SetCap")
	}
	s.Cap = n
}

// SetMapIndex sets the value associated with key in the map v to val.
// It panics if v's Kind is not Map.
// If val is the zero Value, SetMapIndex deletes the key from the map.
// Otherwise if v holds a nil map, SetMapIndex will panic.
// As in Go, key's value must be assignable to the map's key type,
// and val's value must be assignable to the map's value type.
func (v Value) SetMapIndex(key, val Value) {
	v.mustBe(Map)
	v.mustBeExported()
	key.mustBeExported()
	tt := (*mapType)(unsafe.Pointer(v.typ))
	key = key.assignTo("reflect.Value.SetMapIndex", tt.key, nil)
	var k unsafe.Pointer
	if key.flag&flagIndir != 0 {
		k = key.ptr
	} else if key.typ.pointers() {
		k = unsafe.Pointer(&key.ptr)
	} else {
		// k = unsafe.Pointer(&key.scalar)
		panic("reflect: missing flagIndir")
	}
	if val.typ == nil {
		mapdelete(v.typ, v.pointer(), k)
		return
	}
	val.mustBeExported()
	val = val.assignTo("reflect.Value.SetMapIndex", tt.elem, nil)
	var e unsafe.Pointer
	if val.flag&flagIndir != 0 {
		e = val.ptr
	} else if val.typ.pointers() {
		e = unsafe.Pointer(&val.ptr)
	} else {
		// e = unsafe.Pointer(&val.scalar)
		panic("reflect: missing flagIndir")
	}
	mapassign(v.typ, v.pointer(), k, e)
}

// SetUint sets v's underlying value to x.
// It panics if v's Kind is not Uint, Uintptr, Uint8, Uint16, Uint32, or Uint64, or if CanSet() is false.
func (v Value) SetUint(x uint64) {
	v.mustBeAssignable()
	switch k := v.kind(); k {
	default:
		panic(&ValueError{"reflect.Value.SetUint", k})
	case Uint:
		*(*uint)(v.ptr) = uint(x)
	case Uint8:
		*(*uint8)(v.ptr) = uint8(x)
	case Uint16:
		*(*uint16)(v.ptr) = uint16(x)
	case Uint32:
		*(*uint32)(v.ptr) = uint32(x)
	case Uint64:
		*(*uint64)(v.ptr) = x
	case Uintptr:
		*(*uintptr)(v.ptr) = uintptr(x)
	}
}

// SetPointer sets the unsafe.Pointer value v to x.
// It panics if v's Kind is not UnsafePointer.
func (v Value) SetPointer(x unsafe.Pointer) {
	v.mustBeAssignable()
	v.mustBe(UnsafePointer)
	*(*unsafe.Pointer)(v.ptr) = x
}

// SetString sets v's underlying value to x.
// It panics if v's Kind is not String or if CanSet() is false.
func (v Value) SetString(x string) {
	v.mustBeAssignable()
	v.mustBe(String)
	*(*string)(v.ptr) = x
}

// Slice returns v[i:j].
// It panics if v's Kind is not Array, Slice or String, or if v is an unaddressable array,
// or if the indexes are out of bounds.
func (v Value) Slice(i, j int) Value {
	var (
		cap  int
		typ  *sliceType
		base unsafe.Pointer
	)
	switch kind := v.kind(); kind {
	default:
		panic(&ValueError{"reflect.Value.Slice", kind})

	case Array:
		if v.flag&flagAddr == 0 {
			panic("reflect.Value.Slice: slice of unaddressable array")
		}
		tt := (*arrayType)(unsafe.Pointer(v.typ))
		cap = int(tt.len)
		typ = (*sliceType)(unsafe.Pointer(tt.slice))
		base = v.ptr

	case Slice:
		typ = (*sliceType)(unsafe.Pointer(v.typ))
		s := (*sliceHeader)(v.ptr)
		base = unsafe.Pointer(s.Data)
		cap = s.Cap

	case String:
		s := (*stringHeader)(v.ptr)
		if i < 0 || j < i || j > s.Len {
			panic("reflect.Value.Slice: string slice index out of bounds")
		}
		t := stringHeader{unsafe.Pointer(uintptr(s.Data) + uintptr(i)), j - i}
		return Value{v.typ, unsafe.Pointer(&t) /* 0, */, v.flag}
	}

	if i < 0 || j < i || j > cap {
		panic("reflect.Value.Slice: slice index out of bounds")
	}

	// Declare slice so that gc can see the base pointer in it.
	var x []unsafe.Pointer

	// Reinterpret as *sliceHeader to edit.
	s := (*sliceHeader)(unsafe.Pointer(&x))
	s.Data = unsafe.Pointer(uintptr(base) + uintptr(i)*typ.elem.Size())
	s.Len = j - i
	s.Cap = cap - i

	fl := v.flag&flagRO | flagIndir | flag(Slice)<<flagKindShift
	return Value{typ.common(), unsafe.Pointer(&x) /* 0, */, fl}
}

// Slice3 is the 3-index form of the slice operation: it returns v[i:j:k].
// It panics if v's Kind is not Array or Slice, or if v is an unaddressable array,
// or if the indexes are out of bounds.
func (v Value) Slice3(i, j, k int) Value {
	var (
		cap  int
		typ  *sliceType
		base unsafe.Pointer
	)
	switch kind := v.kind(); kind {
	default:
		panic(&ValueError{"reflect.Value.Slice3", kind})

	case Array:
		if v.flag&flagAddr == 0 {
			panic("reflect.Value.Slice3: slice of unaddressable array")
		}
		tt := (*arrayType)(unsafe.Pointer(v.typ))
		cap = int(tt.len)
		typ = (*sliceType)(unsafe.Pointer(tt.slice))
		base = v.ptr

	case Slice:
		typ = (*sliceType)(unsafe.Pointer(v.typ))
		s := (*sliceHeader)(v.ptr)
		base = s.Data
		cap = s.Cap
	}

	if i < 0 || j < i || k < j || k > cap {
		panic("reflect.Value.Slice3: slice index out of bounds")
	}

	// Declare slice so that the garbage collector
	// can see the base pointer in it.
	var x []unsafe.Pointer

	// Reinterpret as *sliceHeader to edit.
	s := (*sliceHeader)(unsafe.Pointer(&x))
	s.Data = unsafe.Pointer(uintptr(base) + uintptr(i)*typ.elem.Size())
	s.Len = j - i
	s.Cap = k - i

	fl := v.flag&flagRO | flagIndir | flag(Slice)<<flagKindShift
	return Value{typ.common(), unsafe.Pointer(&x) /* 0, */, fl}
}

// String returns the string v's underlying value, as a string.
// String is a special case because of Go's String method convention.
// Unlike the other getters, it does not panic if v's Kind is not String.
// Instead, it returns a string of the form "<T value>" where T is v's type.
func (v Value) String() string {
	switch k := v.kind(); k {
	case Invalid:
		return "<invalid Value>"
	case String:
		return *(*string)(v.ptr)
	}
	// If you call String on a reflect.Value of other type, it's better to
	// print something than to panic. Useful in debugging.
	return "<" + v.typ.String() + " Value>"
}

// TryRecv attempts to receive a value from the channel v but will not block.
// It panics if v's Kind is not Chan.
// If the receive delivers a value, x is the transferred value and ok is true.
// If the receive cannot finish without blocking, x is the zero Value and ok is false.
// If the channel is closed, x is the zero value for the channel's element type and ok is false.
func (v Value) TryRecv() (x Value, ok bool) {
	v.mustBe(Chan)
	v.mustBeExported()
	return v.recv(true)
}

// TrySend attempts to send x on the channel v but will not block.
// It panics if v's Kind is not Chan.
// It returns true if the value was sent, false otherwise.
// As in Go, x's value must be assignable to the channel's element type.
func (v Value) TrySend(x Value) bool {
	v.mustBe(Chan)
	v.mustBeExported()
	return v.send(x, true)
}

// Type returns v's type.
func (v Value) Type() Type {
	f := v.flag
	if f == 0 {
		panic(&ValueError{"reflect.Value.Type", Invalid})
	}
	if f&flagMethod == 0 {
		// Easy case
		return toType(v.typ)
	}

	// Method value.
	// v.typ describes the receiver, not the method type.
	i := int(v.flag) >> flagMethodShift
	if v.typ.Kind() == Interface {
		// Method on interface.
		tt := (*interfaceType)(unsafe.Pointer(v.typ))
		if i < 0 || i >= len(tt.methods) {
			panic("reflect: internal error: invalid method index")
		}
		m := &tt.methods[i]
		return toType(m.typ)
	}
	// Method on concrete type.
	ut := v.typ.uncommon()
	if ut == nil || i < 0 || i >= len(ut.methods) {
		panic("reflect: internal error: invalid method index")
	}
	m := &ut.methods[i]
	return toType(m.mtyp)
}

// Uint returns v's underlying value, as a uint64.
// It panics if v's Kind is not Uint, Uintptr, Uint8, Uint16, Uint32, or Uint64.
func (v Value) Uint() uint64 {
	k := v.kind()
	var p unsafe.Pointer
	if v.flag&flagIndir != 0 {
		p = v.ptr
	} else {
		// The escape analysis is good enough that &v.scalar
		// does not trigger a heap allocation.
		// p = unsafe.Pointer(&v.scalar)
		switch k {
		case Uint, Uint8, Uint16, Uint32, Uint64, Uintptr:
			panic("reflect: missing flagIndir")
		}
	}
	switch k {
	case Uint:
		return uint64(*(*uint)(p))
	case Uint8:
		return uint64(*(*uint8)(p))
	case Uint16:
		return uint64(*(*uint16)(p))
	case Uint32:
		return uint64(*(*uint32)(p))
	case Uint64:
		return uint64(*(*uint64)(p))
	case Uintptr:
		return uint64(*(*uintptr)(p))
	}
	panic(&ValueError{"reflect.Value.Uint", k})
}

// UnsafeAddr returns a pointer to v's data.
// It is for advanced clients that also import the "unsafe" package.
// It panics if v is not addressable.
func (v Value) UnsafeAddr() uintptr {
	// TODO: deprecate
	if v.typ == nil {
		panic(&ValueError{"reflect.Value.UnsafeAddr", Invalid})
	}
	if v.flag&flagAddr == 0 {
		panic("reflect.Value.UnsafeAddr of unaddressable value")
	}
	return uintptr(v.ptr)
}

// StringHeader is the runtime representation of a string.
// It cannot be used safely or portably and its representation may
// change in a later release.
// Moreover, the Data field is not sufficient to guarantee the data
// it references will not be garbage collected, so programs must keep
// a separate, correctly typed pointer to the underlying data.
type StringHeader struct {
	Data uintptr
	Len  int
}

// stringHeader is a safe version of StringHeader used within this package.
type stringHeader struct {
	Data unsafe.Pointer
	Len  int
}

// SliceHeader is the runtime representation of a slice.
// It cannot be used safely or portably and its representation may
// change in a later release.
// Moreover, the Data field is not sufficient to guarantee the data
// it references will not be garbage collected, so programs must keep
// a separate, correctly typed pointer to the underlying data.
type SliceHeader struct {
	Data uintptr
	Len  int
	Cap  int
}

// sliceHeader is a safe version of SliceHeader used within this package.
type sliceHeader struct {
	Data unsafe.Pointer
	Len  int
	Cap  int
}

func typesMustMatch(what string, t1, t2 Type) {
	if t1 != t2 {
		panic(what + ": " + t1.String() + " != " + t2.String())
	}
}

// grow grows the slice s so that it can hold extra more values, allocating
// more capacity if needed. It also returns the old and new slice lengths.
func grow(s Value, extra int) (Value, int, int) {
	i0 := s.Len()
	i1 := i0 + extra
	if i1 < i0 {
		panic("reflect.Append: slice overflow")
	}
	m := s.Cap()
	if i1 <= m {
		return s.Slice(0, i1), i0, i1
	}
	if m == 0 {
		m = extra
	} else {
		for m < i1 {
			if i0 < 1024 {
				m += m
			} else {
				m += m / 4
			}
		}
	}
	t := MakeSlice(s.Type(), i1, m)
	Copy(t, s)
	return t, i0, i1
}

// Append appends the values x to a slice s and returns the resulting slice.
// As in Go, each x's value must be assignable to the slice's element type.
func Append(s Value, x ...Value) Value {
	s.mustBe(Slice)
	s, i0, i1 := grow(s, len(x))
	for i, j := i0, 0; i < i1; i, j = i+1, j+1 {
		s.Index(i).Set(x[j])
	}
	return s
}

// AppendSlice appends a slice t to a slice s and returns the resulting slice.
// The slices s and t must have the same element type.
func AppendSlice(s, t Value) Value {
	s.mustBe(Slice)
	t.mustBe(Slice)
	typesMustMatch("reflect.AppendSlice", s.Type().Elem(), t.Type().Elem())
	s, i0, i1 := grow(s, t.Len())
	Copy(s.Slice(i0, i1), t)
	return s
}

// Copy copies the contents of src into dst until either
// dst has been filled or src has been exhausted.
// It returns the number of elements copied.
// Dst and src each must have kind Slice or Array, and
// dst and src must have the same element type.
func Copy(dst, src Value) int {
	dk := dst.kind()
	if dk != Array && dk != Slice {
		panic(&ValueError{"reflect.Copy", dk})
	}
	if dk == Array {
		dst.mustBeAssignable()
	}
	dst.mustBeExported()

	sk := src.kind()
	if sk != Array && sk != Slice {
		panic(&ValueError{"reflect.Copy", sk})
	}
	src.mustBeExported()

	de := dst.typ.Elem()
	se := src.typ.Elem()
	typesMustMatch("reflect.Copy", de, se)

	n := dst.Len()
	if sn := src.Len(); n > sn {
		n = sn
	}

	// If sk is an in-line array, cannot take its address.
	// Instead, copy element by element.
	// TODO: memmove would be ok for this (sa = unsafe.Pointer(&v.scalar))
	// if we teach the compiler that ptrs don't escape from memmove.
	if src.flag&flagIndir == 0 {
		for i := 0; i < n; i++ {
			dst.Index(i).Set(src.Index(i))
		}
		return n
	}

	// Copy via memmove.
	var da, sa unsafe.Pointer
	if dk == Array {
		da = dst.ptr
	} else {
		da = (*sliceHeader)(dst.ptr).Data
	}
	if sk == Array {
		sa = src.ptr
	} else {
		sa = (*sliceHeader)(src.ptr).Data
	}
	memmove(da, sa, uintptr(n)*de.Size())
	return n
}

// A runtimeSelect is a single case passed to rselect.
// This must match ../runtime/chan.c:/runtimeSelect
type runtimeSelect struct {
	dir uintptr        // 0, SendDir, or RecvDir
	typ *rtype         // channel type
	ch  unsafe.Pointer // channel
	val unsafe.Pointer // ptr to data (SendDir) or ptr to receive buffer (RecvDir)
}

// rselect runs a select.  It returns the index of the chosen case.
// If the case was a receive, val is filled in with the received value.
// The conventional OK bool indicates whether the receive corresponds
// to a sent value.
//go:noescape
func rselect([]runtimeSelect) (chosen int, recvOK bool)

// A SelectDir describes the communication direction of a select case.
type SelectDir int

// NOTE: These values must match ../runtime/chan.c:/SelectDir.

const (
	_             SelectDir = iota
	SelectSend              // case Chan <- Send
	SelectRecv              // case <-Chan:
	SelectDefault           // default
)

// A SelectCase describes a single case in a select operation.
// The kind of case depends on Dir, the communication direction.
//
// If Dir is SelectDefault, the case represents a default case.
// Chan and Send must be zero Values.
//
// If Dir is SelectSend, the case represents a send operation.
// Normally Chan's underlying value must be a channel, and Send's underlying value must be
// assignable to the channel's element type. As a special case, if Chan is a zero Value,
// then the case is ignored, and the field Send will also be ignored and may be either zero
// or non-zero.
//
// If Dir is SelectRecv, the case represents a receive operation.
// Normally Chan's underlying value must be a channel and Send must be a zero Value.
// If Chan is a zero Value, then the case is ignored, but Send must still be a zero Value.
// When a receive operation is selected, the received Value is returned by Select.
//
type SelectCase struct {
	Dir  SelectDir // direction of case
	Chan Value     // channel to use (for send or receive)
	Send Value     // value to send (for send)
}

// Select executes a select operation described by the list of cases.
// Like the Go select statement, it blocks until at least one of the cases
// can proceed, makes a uniform pseudo-random choice,
// and then executes that case. It returns the index of the chosen case
// and, if that case was a receive operation, the value received and a
// boolean indicating whether the value corresponds to a send on the channel
// (as opposed to a zero value received because the channel is closed).
func Select(cases []SelectCase) (chosen int, recv Value, recvOK bool) {
	// NOTE: Do not trust that caller is not modifying cases data underfoot.
	// The range is safe because the caller cannot modify our copy of the len
	// and each iteration makes its own copy of the value c.
	runcases := make([]runtimeSelect, len(cases))
	haveDefault := false
	for i, c := range cases {
		rc := &runcases[i]
		rc.dir = uintptr(c.Dir)
		switch c.Dir {
		default:
			panic("reflect.Select: invalid Dir")

		case SelectDefault: // default
			if haveDefault {
				panic("reflect.Select: multiple default cases")
			}
			haveDefault = true
			if c.Chan.IsValid() {
				panic("reflect.Select: default case has Chan value")
			}
			if c.Send.IsValid() {
				panic("reflect.Select: default case has Send value")
			}

		case SelectSend:
			ch := c.Chan
			if !ch.IsValid() {
				break
			}
			ch.mustBe(Chan)
			ch.mustBeExported()
			tt := (*chanType)(unsafe.Pointer(ch.typ))
			if ChanDir(tt.dir)&SendDir == 0 {
				panic("reflect.Select: SendDir case using recv-only channel")
			}
			rc.ch = ch.pointer()
			rc.typ = &tt.rtype
			v := c.Send
			if !v.IsValid() {
				panic("reflect.Select: SendDir case missing Send value")
			}
			v.mustBeExported()
			v = v.assignTo("reflect.Select", tt.elem, nil)
			if v.flag&flagIndir != 0 {
				rc.val = v.ptr
			} else if v.typ.pointers() {
				rc.val = unsafe.Pointer(&v.ptr)
			} else {
				// rc.val = unsafe.Pointer(&v.scalar)
				panic("reflect: missing flagIndir")
			}

		case SelectRecv:
			if c.Send.IsValid() {
				panic("reflect.Select: RecvDir case has Send value")
			}
			ch := c.Chan
			if !ch.IsValid() {
				break
			}
			ch.mustBe(Chan)
			ch.mustBeExported()
			tt := (*chanType)(unsafe.Pointer(ch.typ))
			if ChanDir(tt.dir)&RecvDir == 0 {
				panic("reflect.Select: RecvDir case using send-only channel")
			}
			rc.ch = ch.pointer()
			rc.typ = &tt.rtype
			rc.val = unsafe_New(tt.elem)
		}
	}

	chosen, recvOK = rselect(runcases)
	if runcases[chosen].dir == uintptr(SelectRecv) {
		tt := (*chanType)(unsafe.Pointer(runcases[chosen].typ))
		t := tt.elem
		p := runcases[chosen].val
		fl := flag(t.Kind()) << flagKindShift
		if t.Kind() != Ptr && t.Kind() != UnsafePointer {
			recv = Value{t, p /* 0, */, fl | flagIndir}
		} else {
			recv = Value{t, *(*unsafe.Pointer)(p) /* 0, */, fl}
		}
	}
	return chosen, recv, recvOK
}

/*
 * constructors
 */

// implemented in package runtime
func unsafe_New(*rtype) unsafe.Pointer
func unsafe_NewArray(*rtype, int) unsafe.Pointer

// MakeSlice creates a new zero-initialized slice value
// for the specified slice type, length, and capacity.
func MakeSlice(typ Type, len, cap int) Value {
	if typ.Kind() != Slice {
		panic("reflect.MakeSlice of non-slice type")
	}
	if len < 0 {
		panic("reflect.MakeSlice: negative len")
	}
	if cap < 0 {
		panic("reflect.MakeSlice: negative cap")
	}
	if len > cap {
		panic("reflect.MakeSlice: len > cap")
	}

	s := sliceHeader{unsafe_NewArray(typ.Elem().(*rtype), cap), len, cap}
	return Value{typ.common(), unsafe.Pointer(&s) /* 0, */, flagIndir | flag(Slice)<<flagKindShift}
}

// MakeChan creates a new channel with the specified type and buffer size.
func MakeChan(typ Type, buffer int) Value {
	if typ.Kind() != Chan {
		panic("reflect.MakeChan of non-chan type")
	}
	if buffer < 0 {
		panic("reflect.MakeChan: negative buffer size")
	}
	if typ.ChanDir() != BothDir {
		panic("reflect.MakeChan: unidirectional channel type")
	}
	ch := makechan(typ.(*rtype), uint64(buffer))
	return Value{typ.common(), unsafe.Pointer(&ch) /* 0, */, flagIndir | (flag(Chan) << flagKindShift)}
}

// MakeMap creates a new map of the specified type.
func MakeMap(typ Type) Value {
	if typ.Kind() != Map {
		panic("reflect.MakeMap of non-map type")
	}
	m := makemap(typ.(*rtype))
	return Value{typ.common(), unsafe.Pointer(&m) /* 0, */, flagIndir | (flag(Map) << flagKindShift)}
}

// Indirect returns the value that v points to.
// If v is a nil pointer, Indirect returns a zero Value.
// If v is not a pointer, Indirect returns v.
func Indirect(v Value) Value {
	if v.Kind() != Ptr {
		return v
	}
	return v.Elem()
}

// ValueOf returns a new Value initialized to the concrete value
// stored in the interface i.  ValueOf(nil) returns the zero Value.
func ValueOf(i interface{}) Value {
	if i == nil {
		return Value{}
	}

	// TODO(rsc): Eliminate this terrible hack.
	// In the call to unpackEface, i.typ doesn't escape,
	// and i.word is an integer.  So it looks like
	// i doesn't escape.  But really it does,
	// because i.word is actually a pointer.
	escapes(i)

	return unpackEface(i)
}

// Zero returns a Value representing the zero value for the specified type.
// The result is different from the zero value of the Value struct,
// which represents no value at all.
// For example, Zero(TypeOf(42)) returns a Value with Kind Int and value 0.
// The returned value is neither addressable nor settable.
func Zero(typ Type) Value {
	if typ == nil {
		panic("reflect: Zero(nil)")
	}
	t := typ.common()
	fl := flag(t.Kind()) << flagKindShift
	if t.Kind() == Ptr || t.Kind() == UnsafePointer {
		return Value{t, nil /* 0, */, fl}
	}
	return Value{t, unsafe_New(typ.(*rtype)) /* 0, */, fl | flagIndir}
}

// New returns a Value representing a pointer to a new zero value
// for the specified type.  That is, the returned Value's Type is PtrTo(typ).
func New(typ Type) Value {
	if typ == nil {
		panic("reflect: New(nil)")
	}
	ptr := unsafe_New(typ.(*rtype))
	fl := flag(Ptr) << flagKindShift
	return Value{typ.common().ptrTo(), ptr /* 0, */, fl}
}

// NewAt returns a Value representing a pointer to a value of the
// specified type, using p as that pointer.
func NewAt(typ Type, p unsafe.Pointer) Value {
	fl := flag(Ptr) << flagKindShift
	return Value{typ.common().ptrTo(), p /* 0, */, fl}
}

// assignTo returns a value v that can be assigned directly to typ.
// It panics if v is not assignable to typ.
// For a conversion to an interface type, target is a suggested scratch space to use.
func (v Value) assignTo(context string, dst *rtype, target *interface{}) Value {
	if v.flag&flagMethod != 0 {
		v = makeMethodValue(context, v)
	}

	switch {
	case directlyAssignable(dst, v.typ):
		// Overwrite type so that they match.
		// Same memory layout, so no harm done.
		v.typ = dst
		fl := v.flag & (flagRO | flagAddr | flagIndir)
		fl |= flag(dst.Kind()) << flagKindShift
		return Value{dst, v.ptr /* v.scalar, */, fl}

	case implements(dst, v.typ):
		if target == nil {
			target = new(interface{})
		}
		x := valueInterface(v, false)
		if dst.NumMethod() == 0 {
			*target = x
		} else {
			ifaceE2I(dst, x, unsafe.Pointer(target))
		}
		return Value{dst, unsafe.Pointer(target) /* 0, */, flagIndir | flag(Interface)<<flagKindShift}
	}

	// Failed.
	panic(context + ": value of type " + v.typ.String() + " is not assignable to type " + dst.String())
}

// Convert returns the value v converted to type t.
// If the usual Go conversion rules do not allow conversion
// of the value v to type t, Convert panics.
func (v Value) Convert(t Type) Value {
	if v.flag&flagMethod != 0 {
		v = makeMethodValue("Convert", v)
	}
	op := convertOp(t.common(), v.typ)
	if op == nil {
		panic("reflect.Value.Convert: value of type " + v.typ.String() + " cannot be converted to type " + t.String())
	}
	return op(v, t)
}

// convertOp returns the function to convert a value of type src
// to a value of type dst. If the conversion is illegal, convertOp returns nil.
func convertOp(dst, src *rtype) func(Value, Type) Value {
	switch src.Kind() {
	case Int, Int8, Int16, Int32, Int64:
		switch dst.Kind() {
		case Int, Int8, Int16, Int32, Int64, Uint, Uint8, Uint16, Uint32, Uint64, Uintptr:
			return cvtInt
		case Float32, Float64:
			return cvtIntFloat
		case String:
			return cvtIntString
		}

	case Uint, Uint8, Uint16, Uint32, Uint64, Uintptr:
		switch dst.Kind() {
		case Int, Int8, Int16, Int32, Int64, Uint, Uint8, Uint16, Uint32, Uint64, Uintptr:
			return cvtUint
		case Float32, Float64:
			return cvtUintFloat
		case String:
			return cvtUintString
		}

	case Float32, Float64:
		switch dst.Kind() {
		case Int, Int8, Int16, Int32, Int64:
			return cvtFloatInt
		case Uint, Uint8, Uint16, Uint32, Uint64, Uintptr:
			return cvtFloatUint
		case Float32, Float64:
			return cvtFloat
		}

	case Complex64, Complex128:
		switch dst.Kind() {
		case Complex64, Complex128:
			return cvtComplex
		}

	case String:
		if dst.Kind() == Slice && dst.Elem().PkgPath() == "" {
			switch dst.Elem().Kind() {
			case Uint8:
				return cvtStringBytes
			case Int32:
				return cvtStringRunes
			}
		}

	case Slice:
		if dst.Kind() == String && src.Elem().PkgPath() == "" {
			switch src.Elem().Kind() {
			case Uint8:
				return cvtBytesString
			case Int32:
				return cvtRunesString
			}
		}
	}

	// dst and src have same underlying type.
	if haveIdenticalUnderlyingType(dst, src) {
		return cvtDirect
	}

	// dst and src are unnamed pointer types with same underlying base type.
	if dst.Kind() == Ptr && dst.Name() == "" &&
		src.Kind() == Ptr && src.Name() == "" &&
		haveIdenticalUnderlyingType(dst.Elem().common(), src.Elem().common()) {
		return cvtDirect
	}

	if implements(dst, src) {
		if src.Kind() == Interface {
			return cvtI2I
		}
		return cvtT2I
	}

	return nil
}

// makeInt returns a Value of type t equal to bits (possibly truncated),
// where t is a signed or unsigned int type.
func makeInt(f flag, bits uint64, t Type) Value {
	typ := t.common()
	if typ.size > ptrSize {
		// Assume ptrSize >= 4, so this must be uint64.
		ptr := unsafe_New(typ)
		*(*uint64)(unsafe.Pointer(ptr)) = bits
		return Value{typ, ptr /* 0, */, f | flagIndir | flag(typ.Kind())<<flagKindShift}
	}
	var s uintptr
	switch typ.size {
	case 1:
		*(*uint8)(unsafe.Pointer(&s)) = uint8(bits)
	case 2:
		*(*uint16)(unsafe.Pointer(&s)) = uint16(bits)
	case 4:
		*(*uint32)(unsafe.Pointer(&s)) = uint32(bits)
	case 8:
		*(*uint64)(unsafe.Pointer(&s)) = uint64(bits)
	}
	return Value{typ, unsafe.Pointer(&s) /* 0, */, f | flagIndir | flag(typ.Kind())<<flagKindShift}
}

// makeFloat returns a Value of type t equal to v (possibly truncated to float32),
// where t is a float32 or float64 type.
func makeFloat(f flag, v float64, t Type) Value {
	typ := t.common()
	if typ.size > ptrSize {
		// Assume ptrSize >= 4, so this must be float64.
		ptr := unsafe_New(typ)
		*(*float64)(unsafe.Pointer(ptr)) = v
		return Value{typ, ptr /* 0, */, f | flagIndir | flag(typ.Kind())<<flagKindShift}
	}

	var s uintptr
	switch typ.size {
	case 4:
		*(*float32)(unsafe.Pointer(&s)) = float32(v)
	case 8:
		*(*float64)(unsafe.Pointer(&s)) = v
	}
	return Value{typ, unsafe.Pointer(&s) /* 0, */, f | flagIndir | flag(typ.Kind())<<flagKindShift}
}

// makeComplex returns a Value of type t equal to v (possibly truncated to complex64),
// where t is a complex64 or complex128 type.
func makeComplex(f flag, v complex128, t Type) Value {
	typ := t.common()
	if typ.size > ptrSize {
		ptr := unsafe_New(typ)
		switch typ.size {
		case 8:
			*(*complex64)(unsafe.Pointer(ptr)) = complex64(v)
		case 16:
			*(*complex128)(unsafe.Pointer(ptr)) = v
		}
		return Value{typ, ptr /* 0, */, f | flagIndir | flag(typ.Kind())<<flagKindShift}
	}

	// Assume ptrSize <= 8 so this must be complex64.
	var s uintptr
	*(*complex64)(unsafe.Pointer(&s)) = complex64(v)
	return Value{typ, unsafe.Pointer(&s) /* 0, */, f | flagIndir | flag(typ.Kind())<<flagKindShift}
}

func makeString(f flag, v string, t Type) Value {
	ret := New(t).Elem()
	ret.SetString(v)
	ret.flag = ret.flag&^flagAddr | f | flagIndir
	return ret
}

func makeBytes(f flag, v []byte, t Type) Value {
	ret := New(t).Elem()
	ret.SetBytes(v)
	ret.flag = ret.flag&^flagAddr | f | flagIndir
	return ret
}

func makeRunes(f flag, v []rune, t Type) Value {
	ret := New(t).Elem()
	ret.setRunes(v)
	ret.flag = ret.flag&^flagAddr | f | flagIndir
	return ret
}

// These conversion functions are returned by convertOp
// for classes of conversions. For example, the first function, cvtInt,
// takes any value v of signed int type and returns the value converted
// to type t, where t is any signed or unsigned int type.

// convertOp: intXX -> [u]intXX
func cvtInt(v Value, t Type) Value {
	return makeInt(v.flag&flagRO, uint64(v.Int()), t)
}

// convertOp: uintXX -> [u]intXX
func cvtUint(v Value, t Type) Value {
	return makeInt(v.flag&flagRO, v.Uint(), t)
}

// convertOp: floatXX -> intXX
func cvtFloatInt(v Value, t Type) Value {
	return makeInt(v.flag&flagRO, uint64(int64(v.Float())), t)
}

// convertOp: floatXX -> uintXX
func cvtFloatUint(v Value, t Type) Value {
	return makeInt(v.flag&flagRO, uint64(v.Float()), t)
}

// convertOp: intXX -> floatXX
func cvtIntFloat(v Value, t Type) Value {
	return makeFloat(v.flag&flagRO, float64(v.Int()), t)
}

// convertOp: uintXX -> floatXX
func cvtUintFloat(v Value, t Type) Value {
	return makeFloat(v.flag&flagRO, float64(v.Uint()), t)
}

// convertOp: floatXX -> floatXX
func cvtFloat(v Value, t Type) Value {
	return makeFloat(v.flag&flagRO, v.Float(), t)
}

// convertOp: complexXX -> complexXX
func cvtComplex(v Value, t Type) Value {
	return makeComplex(v.flag&flagRO, v.Complex(), t)
}

// convertOp: intXX -> string
func cvtIntString(v Value, t Type) Value {
	return makeString(v.flag&flagRO, string(v.Int()), t)
}

// convertOp: uintXX -> string
func cvtUintString(v Value, t Type) Value {
	return makeString(v.flag&flagRO, string(v.Uint()), t)
}

// convertOp: []byte -> string
func cvtBytesString(v Value, t Type) Value {
	return makeString(v.flag&flagRO, string(v.Bytes()), t)
}

// convertOp: string -> []byte
func cvtStringBytes(v Value, t Type) Value {
	return makeBytes(v.flag&flagRO, []byte(v.String()), t)
}

// convertOp: []rune -> string
func cvtRunesString(v Value, t Type) Value {
	return makeString(v.flag&flagRO, string(v.runes()), t)
}

// convertOp: string -> []rune
func cvtStringRunes(v Value, t Type) Value {
	return makeRunes(v.flag&flagRO, []rune(v.String()), t)
}

// convertOp: direct copy
func cvtDirect(v Value, typ Type) Value {
	f := v.flag
	t := typ.common()
	ptr := v.ptr
	if f&flagAddr != 0 {
		// indirect, mutable word - make a copy
		c := unsafe_New(t)
		memmove(c, ptr, t.size)
		ptr = c
		f &^= flagAddr
	}
	return Value{t, ptr /* v.scalar, */, v.flag&flagRO | f} // v.flag&flagRO|f == f?
}

// convertOp: concrete -> interface
func cvtT2I(v Value, typ Type) Value {
	target := new(interface{})
	x := valueInterface(v, false)
	if typ.NumMethod() == 0 {
		*target = x
	} else {
		ifaceE2I(typ.(*rtype), x, unsafe.Pointer(target))
	}
	return Value{typ.common(), unsafe.Pointer(target) /* 0, */, v.flag&flagRO | flagIndir | flag(Interface)<<flagKindShift}
}

// convertOp: interface -> interface
func cvtI2I(v Value, typ Type) Value {
	if v.IsNil() {
		ret := Zero(typ)
		ret.flag |= v.flag & flagRO
		return ret
	}
	return cvtT2I(v.Elem(), typ)
}

// implemented in ../pkg/runtime
func chancap(ch unsafe.Pointer) int
func chanclose(ch unsafe.Pointer)
func chanlen(ch unsafe.Pointer) int

//go:noescape
func chanrecv(t *rtype, ch unsafe.Pointer, nb bool, val unsafe.Pointer) (selected, received bool)

//go:noescape
func chansend(t *rtype, ch unsafe.Pointer, val unsafe.Pointer, nb bool) bool

func makechan(typ *rtype, size uint64) (ch unsafe.Pointer)
func makemap(t *rtype) (m unsafe.Pointer)
func mapaccess(t *rtype, m unsafe.Pointer, key unsafe.Pointer) (val unsafe.Pointer)
func mapassign(t *rtype, m unsafe.Pointer, key, val unsafe.Pointer)
func mapdelete(t *rtype, m unsafe.Pointer, key unsafe.Pointer)
func mapiterinit(t *rtype, m unsafe.Pointer) unsafe.Pointer
func mapiterkey(it unsafe.Pointer) (key unsafe.Pointer)
func mapiternext(it unsafe.Pointer)
func maplen(m unsafe.Pointer) int

func call(typ *rtype, fnaddr unsafe.Pointer, isInterface bool, isMethod bool, params *unsafe.Pointer, results *unsafe.Pointer)
func ifaceE2I(t *rtype, src interface{}, dst unsafe.Pointer)

// Dummy annotation marking that the value x escapes,
// for use in cases where the reflect code is so clever that
// the compiler cannot follow.
func escapes(x interface{}) {
	if dummy.b {
		dummy.x = x
	}
}

var dummy struct {
	b bool
	x interface{}
}
