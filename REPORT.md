# Mini-Go Compiler -- Report

## 1. Typing

### Multi-phase structure resolution

Struct types are resolved in three separate passes over the declaration list before any function body is typed:

1. **Phase 1** registers all struct names (empty shells) into `env_structs`, ensuring uniqueness.
2. **Phase 2** populates each struct's fields, resolving field types against the now-complete struct name table. This two-phase approach allows structs to reference each other (e.g. `A` has a field of type `*B` and `B` has a field of type `*A`) without requiring forward declarations.
3. **Phase 3** (`check_recursive_structs`) performs a DFS over field types to detect illegal direct recursion (e.g. struct `S` containing a field of type `S`), while still permitting pointer-based recursion (`*S`).

### Scope management with a stack of hash tables

Variable scopes are modeled as a `Hashtbl list` passed through `type_expr`. Each `PEblock` pushes a fresh table; lookups walk the list from innermost to outermost. When the block ends, the scope is checked for unused variables (Go semantics) and naturally discarded. This avoids the need for an explicit scope-close operation and keeps shadowing correct -- `mem_current_scope` only checks the innermost table, so redeclaring a variable in a nested scope is allowed while redeclaring in the same scope is rejected.

### Function environment and recursion

Functions are registered in `env_funcs` _before_ their body is typed. This allows direct recursion. Mutual recursion between functions is also supported because all declarations are processed sequentially into the same shared `env_funcs` table (as long as the function called is declared before the caller in source order).

### Type compatibility with `nil`

The `type_assignable` function encodes Go's rule that `nil` is assignable to any pointer type.

### `is_returns` for return checking

`is_returns` recursively checks that all control paths in a function body end with a `return`. It requires both branches of an `if` to return, and conservatively returns `false` for `for` loops (since the compiler cannot prove the loop body always executes).

### Variable declarations with initializers

`PEvars` handles both `var x int` (no initializer) and `var x int = 42` (with initializer). When there is no explicit type annotation, the type is inferred from the initializer. The result is a `TEblock [TEvars vars; TEassign ...]`, which is important rewriting.

## 2. AST Rewriting (`rewrite.ml`) -- ADDED Section

The **ADDED section** (two extra match cases in `block`) handles a case the original code did not cover: **variable declarations wrapped inside a `TEblock`**. This happens when `typing.ml` produces a variable declaration _with an initializer_, which is represented as:

```
TEblock [TEvars [v]; TEassign ([v], [init_expr])]
```

Without the added cases, the rewrite pass would see a `TEblock` node (not a bare `TEvars`) at the head of the outer block, skip the RW3/RW4 transformation, and process it as a generic expression. The struct variable or address-taken variable would remain on the stack instead of being heap-allocated, leading to incorrect code generation.

The two added cases are:

1. **Struct/address-taken variable inside a nested block**: When the outer block starts with `TEblock [TEvars (v::_ as vl); ...inner_bl...]` and `v` is a struct or has its address taken, it applies the same RW3/RW4 transformation (replace `v` with a fresh pointer `v'`, allocate via `new`, substitute `*v'` for `v` everywhere) and then flattens the inner block's remaining statements into the outer block for further processing.

2. **Non-struct variable inside a nested block**: When the nested `TEblock` starts with `TEvars` but the variable does not need heap allocation, the inner block is simply flattened into the outer block (`block rw (inner_bl @ bl)`), ensuring subsequent statements are still processed.

This handles patterns like `var dico *BST = nil` where the typed AST produces `TEblock [TEvars [dico]; TEassign ([dico], [nil])]`.

## 3. Code Generation

### Stack-only calling convention

All function parameters are passed exclusively on the stack. The compiler does not use any register-based parameter passing.

**Caller side (`compile_call`):**

1. Optional padding for 16-byte alignment
2. Reserve space for return values (`subq ret_space, %rsp`)
3. Push all arguments right-to-left onto the stack
4. `call F_name`
5. Clean up argument space (`addq stack_arg_space, %rsp`)
6. Read return values (now at top of stack)

**Callee side (`compile_decl`):**
After the standard prologue (`push %rbp; mov %rsp, %rbp`), the callee's stack frame looks like:

```
[%rbp + 16]                    = param 0
[%rbp + 16 + 8]                = param 1
...
[%rbp + 16 + 8*(n-1)]         = param n-1
[%rbp + 16 + 8*n]             = return slot 0 (if any)
[%rbp]                         = saved %rbp
[%rbp - 8], [%rbp - 16], ...  = local variables
```

Parameters are accessed directly from the caller's frame (positive offsets from `%rbp`), so no register-to-stack spilling is needed in the prologue. Local variables are allocated at negative offsets starting from 0 (`allocate_locals_expr 0 body`).

### Return value mechanism

For single-return functions, `TEreturn [e]` evaluates the expression into `%rax`, then stores it at `[%rbp + 16 + 8 * num_params]` (the return slot, located just above all parameters on the caller's frame). After the callee returns, the caller pops this value into `%rax`. For void functions (`TEreturn []`), execution simply jumps to the epilogue label.

### Null pointer safety

The compiler inserts null checks (`testq %rax, %rax; jz graceful_stop`) before every pointer dereference: field access through a pointer (`TEdot` with `Tptr`), explicit dereference (`Ustar`), and address computation through pointers (`compile_addr`). The `graceful_stop` label calls `exit(1)` to terminate cleanly rather than segfaulting.

### Testing

- All tests have passed
- No new test added.
