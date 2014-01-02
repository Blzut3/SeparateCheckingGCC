// { dg-options "-std=gnu++11" }
// { dg-do compile }

// Copyright (C) 2013-2014 Free Software Foundation, Inc.
//
// This file is part of the GNU ISO C++ Library.  This library is free
// software; you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the
// Free Software Foundation; either version 3, or (at your option)
// any later version.

// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License along
// with this library; see the file COPYING3.  If not see
// <http://www.gnu.org/licenses/>.

#include <ext/vstring.h>

void test01() 
{
  __gnu_cxx::__wvstring wvs1;
  wvs1.replace(wvs1.cbegin(), wvs1.cend(), wvs1);
  wvs1.replace(wvs1.cbegin(), wvs1.cend(), L"1", 1);
  wvs1.replace(wvs1.cbegin(), wvs1.cend(), L"2");
  wvs1.replace(wvs1.cbegin(), wvs1.cend(), 1, L'3');
  wvs1.replace(wvs1.cbegin(), wvs1.cend(), wvs1.begin(), wvs1.end());
  wvs1.replace(wvs1.cbegin(), wvs1.cend(), {'4', '5'});
}
