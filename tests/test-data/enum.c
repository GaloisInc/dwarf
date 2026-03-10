//# --debug-info
//@ -gdwarf-4
enum Color { RED, GREEN, BLUE };

int main(void) {
    enum Color c = RED;
    return c;
}
