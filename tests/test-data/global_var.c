//# --debug-info
//@ -gdwarf-4
//%  gcc-13-x86_64 clang-16-x86_64 clang-17-x86_64 clang-18-x86_64
//%  gcc-13-aarch64  clang-18-aarch64
//%  gcc-13-aarch32  clang-18-aarch32
//%  gcc-13-ppc32    clang-18-ppc32
//%  gcc-13-ppc64    clang-18-ppc64
int global_var = 42;

int main(void) {
    return global_var;
}
