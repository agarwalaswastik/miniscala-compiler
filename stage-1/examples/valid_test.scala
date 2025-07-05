def fib(x: Int): Int = {
  if (x <= 1) {
    x
  } else {
    fib(x - 1) + fib(x - 2)
  }
};
val arr = new Array[Int](5);
var i = 0;
while (i < 5) {
  arr(i) = fib(i + 5);
  i = i + 1
};
arr(4)
