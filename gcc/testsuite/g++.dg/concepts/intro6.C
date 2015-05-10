// { dg-options "-std=c++1z" }

// Test for potential regression with template introduction tentative parses.

template<typename>
struct S1
{
	static constexpr bool ne();
};

namespace NS1 { template<typename> class S2 {}; }

template<typename T>
class S3
{
	void swap() noexcept(S1<T>::ne()) {}

	NS1::S2<T> f2();
};

int main() { return 0; }
