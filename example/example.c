#include<stdio.h>
int main() {

    int x;
    int y = 3;
    scanf("%d", &x);

    if(x < 5) {
        y++;
        x++;
        printf("in if\n");
    }

    if(y == 4) {
        y++;
    }

    printf("%d\n", y);

    printf("out of if\n");

    return 0;
}
