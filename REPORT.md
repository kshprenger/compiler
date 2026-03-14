# Mini-Go Compiler -- Report

## 1. Typing

### Multi-phase structure resolution

Struct types are resolved in three separate passes over the declaration list before any function body is typed:

1. **Phase 1** registers all struct names as empty shells into `env_structs`, ensuring uniqueness and making every struct name visible to subsequent passes.
2. **Phase 2** populates each struct's fields, resolving field types against the now-complete struct name table. This two-phase approach allows mutually referential structs (e.g. `A` has a field of type `*B` and `B` has a field of type `*A`) without requiring forward declarations.
3. **Phase 3** (`check_recursive_structs`) performs a DFS over field types to detect illegal direct value recursion (e.g. struct `S` with a field of type `S`), while allowing pointer-based recursion (`*S`). It is a separate pass to keep the recursive-check logic isolated from field resolution.

### Scope management with a stack of hash tables

Variable scopes are modeled as a `Hashtbl list` passed through `type_expr`. Each `PEblock` pushes a fresh table onto the front of the list; lookups walk the list from innermost to outermost, implementing lexical scoping. When a block ends, its table is checked for unused variables (Go semantics require all declared variables to be used) and then naturally discarded. The helper `mem_current_scope` only tests the innermost table, so shadowing a variable in a nested block is permitted while redeclaring it in the same scope is an error.

### Function environment and recursion

Functions are registered in `env_funcs` before their body is typed, which enables direct recursion: the function can call itself by name because its signature is already in the environment when the body is checked. Mutual recursion is also supported as long as functions are declared in dependency order, since all declarations share the same `env_funcs` table and are processed top-to-bottom.

### Type compatibility with `nil`

The `type_assignable` predicate encodes Go's rule that `nil` is a valid value for any pointer type. This is checked whenever an expression is assigned to a variable, passed as a function argument, or returned -- allowing idiomatic patterns like `return nil` for pointer-returning functions without special-casing at every use site.

### `is_returns` for return checking

`is_returns` recursively verifies that all control paths through a function body terminate with a `return`. An `if` statement satisfies this only when both its `then` and `else` branches return. `for` loops are conservatively treated as non-returning because the compiler cannot statically prove that the loop body executes at least once. This is consistent with Go's specification.

### Variable declarations with initializers

`PEvars` handles both `var x T` (default-initialized) and `var x T = e` (explicit initializer). When no type annotation is given, the type is inferred from the initializer expression. Internally, a declaration with an initializer is desugared into `TEblock [TEvars vars; TEassign (vars, inits)]` -- a block that first declares the variables and then immediately assigns them. This representation is significant for the rewrite pass.

## 2. AST Rewriting (`rewrite.ml`) -- ADDED Section

The added section introduces two extra match cases in the `block` function to handle **variable declarations wrapped inside a nested `TEblock`**. This wrapping occurs whenever `typing.ml` desugars a declaration with an initializer, producing:

```
TEblock [TEvars [v]; TEassign ([v], [init_expr])]
```

Without these cases, the rewrite pass encounters a `TEblock` node at the head of the outer block instead of a bare `TEvars`, misses the RW3/RW4 heap-allocation transformation, and processes the nested block as a generic expression. Any struct variable or address-taken variable would then remain stack-allocated rather than heap-allocated, producing incorrect code generation for anything involving pointers to locals.

The two added cases are:

1. **Struct or address-taken variable inside a nested block**: When the outer block's first element is `TEblock [TEvars (v::_ as vl); ...inner_bl...]` and `v` is a struct type or has its address taken elsewhere in the program, the same RW3/RW4 transformation is applied -- `v` is replaced by a fresh pointer variable `v'`, a `new` allocation is emitted, and every occurrence of `v` in the remaining code is substituted by `*v'`. The inner block's remaining statements are then flattened into the outer block so that subsequent rewrite passes continue normally.

2. **Non-heap variable inside a nested block**: When the nested `TEblock` begins with a `TEvars` but the variable does not require heap allocation, the inner block is simply flattened into the outer block via `block rw (inner_bl @ bl)`. This ensures all remaining statements are still processed by the rewrite pass rather than left untransformed.

A concrete example: `var dico *BST = nil` produces `TEblock [TEvars [dico]; TEassign ([dico], [nil])]` in the typed AST. Without the fix, `dico` would not be correctly identified as address-taken, and the rewrite would silently skip its transformation.

## 3. Code Generation

### Stack-only calling convention

All function parameters are passed exclusively on the stack; no System V AMD64 register arguments are used. This simplifies code generation at the cost of slightly higher memory traffic.

**Caller side (`compile_call`):**

1. Optionally pad the stack to maintain 16-byte alignment before the call.
2. Reserve space for return values by subtracting `ret_space` from `%rsp`.
3. Push all arguments right-to-left so that the first argument ends up at the lowest address above the return slots.
4. Emit `call F_name`.
5. Reclaim argument space by adding `stack_arg_space` back to `%rsp`.
6. Read return values from the top of the stack.

**Callee side (`compile_decl`):**

After the standard prologue (`push %rbp; mov %rsp, %rbp`), parameters are at positive offsets from `%rbp` (they live in the caller's frame above the saved return address and saved `%rbp`), and local variables occupy negative offsets. The first parameter is at `[%rbp + 16]`, subsequent parameters at `[%rbp + 16 + 8*i]`, and the return slot (if any) immediately above the last parameter. Local variable offsets are computed by `allocate_locals_expr 0 body`, which walks the body and assigns a negative offset to each declared local.

### Return value mechanism

For single-return functions, `TEreturn [e]` evaluates the expression and stores the result at the return slot `[%rbp + 16 + 8 * num_params]` in the caller's frame before jumping to the epilogue. The caller then reads the value from the top of the stack after the `call` returns. For void functions (`TEreturn []`), the epilogue is reached directly without any store.

### Null pointer safety

Before every pointer dereference, the compiler emits a null check: it loads the pointer into `%rax`, executes `testq %rax, %rax`, and jumps to `graceful_stop` if the result is zero. This check is inserted at three points: field access through a pointer (`TEdot` when the expression has type `Tptr`), explicit pointer dereference (`Ustar`), and address computation through a pointer in `compile_addr`. The `graceful_stop` routine calls `exit(1)`, producing a clean error exit rather than a segmentation fault.

### Testing

- All provided tests pass.
- No new tests were added.
