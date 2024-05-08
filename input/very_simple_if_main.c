#include <stdio.h>
#include <stdbool.h>

extern int very_simple_if(bool x, bool y);

int main() {
#define check(x, y, expected) printf("very_simple_if(" #x ", " #y ") = %d == %d\n", very_simple_if(x, y), expected)
    check(false, false, 0);
    check(false, true, 1);
    check(true, false, 2);
    check(true, true, 3);
}
