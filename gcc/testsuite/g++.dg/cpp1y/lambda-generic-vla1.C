// PR c++/59271
// { dg-do compile { target c++14 } }

extern "C" int printf (const char *, ...);

void f(int n)
{
  int  a[n];

  for (auto& i : a)
    {
      i = &i - a;
    }

  [&a] (auto m)
    {
      for (auto i : a)
	{
	  printf ("%d", i);
	}

      return m;
    };
}
