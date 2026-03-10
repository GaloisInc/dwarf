//# --debug-info
//@ -gdwarf-4
struct Point {
    int x;
    int y;
};

int main(void) {
    struct Point p = {10, 20};
    return p.x;
}
