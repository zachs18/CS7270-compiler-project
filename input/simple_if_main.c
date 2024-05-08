#include <stdio.h>

extern int bad_fizzbuzz(int);

int main() {
    for (int i = 0; i < 45; ++i) {
        printf("%d: %d\n", i, bad_fizzbuzz(i));
    }
}
