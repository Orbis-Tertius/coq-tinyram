int fact (int x) {
  int y = 1;
  while (x > 0) {
    y = y * x;
    x = x - 1;
  }
  return y;
}

int main () {
  if (fact(4) == 24 && fact(5) == 120) {
    return 0;
  } else {
    return 1;
  }
}
