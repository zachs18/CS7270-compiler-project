#include <stdio.h>
#include <stdint.h>

extern void bubble_sort(uint32_t *array, size_t length);

int main() {
    uint32_t array[24] = {957412227, 1209599327, 3824981732, 642572600, 2283481974, 2205016556, 2326244601, 3518510655, 457813396, 2077216112, 1523343182, 420060718, 3910959292, 678790184, 100893879, 1584152289, 3240246140, 1761707760, 2889627943, 4093032465, 825446985, 91675502, 3157852842, 1539525348};
    printf("array = {%u", array[0]);
    for (size_t i = 1; i < 24; ++i) {
        printf(", %u", array[i]);
    }
    printf("}\n");
    printf("\n");
    printf("sorting...\n");

    bubble_sort(array, 24);
    uint32_t expected[24]= {91675502, 100893879, 420060718, 457813396, 642572600, 678790184, 825446985, 957412227, 1209599327, 1523343182, 1539525348, 1584152289, 1761707760, 2077216112, 2205016556, 2283481974, 2326244601, 2889627943, 3157852842, 3240246140, 3518510655, 3824981732, 3910959292, 4093032465};

    for (size_t i = 0; i < 24; ++i) {
        if (array[i] == expected[i]) printf("array[i] is correct\n");
        else printf("array[i] is NOT correct (expected %u, found %u)\n", expected[i], array[i]);
    }
}
