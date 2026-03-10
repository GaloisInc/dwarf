//# --debug-info
//@ -gdwarf-4
union Data {
    int i;
    float f;
};

int main(void) {
    union Data d;
    d.i = 42;
    return d.i;
}
