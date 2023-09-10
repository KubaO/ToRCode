This is a little module that takes a Real-valued Mathematica expression, finds the free variables in it, and spits out the result as an R function that returns the floating point value.



The `expressions` folder contains some test expressions.



The following Mathematica forms are handled:

- scalar addition, subtraction, division, multiplication, raising to a power
- transcendental functions that have C equivalents
- `Root` forms - translated to `polyroot`.



It works roughly as follows:

1. Root forms, if any, are taken out of the expression and are replaced by variables.
2. The expression is translated to SymbolicC form.
3. The symbolic C form is massaged to make it work with R.
   - Constants are propagated from within the initialization function into the function that computes the expression's value.
   - Partial constant propagation is applied within the compute function.
   - The unrolled integer power-raising code is replaced by `pow` calls.
   - The function's signature is changed to return the `double` result.
4. Polynomial root finding calls are generated if needed.
5. Symbolic C is converted to C program text.
6. The C program syntax is morphed to make it valid R syntax:
   - function definition syntax is adapted
   - `pow(b,e)` is replaced by `b^e`
   - semicolons are removed

