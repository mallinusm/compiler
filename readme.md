# Compilers 2021

Multi-pass compiler.

## Passes

- check-paren-x64
- check-paren-x64-syntax
- check-paren-x64-init
- interp-paren-x64
- generate-x64
- wrap-x64-run-time
- wrap-x64-boilerplate
- implement-fvars
- patch-instructions
- flatten-begins
- replace-locations
- assign-fvars
- uncover-locals
- assign-homes
- select-instructions
- canonicalize-bind
- sequentialize-let
- uniquify
- undead-analysis
- conflict-analysis
- assign-registers
- assign-homes-opt
- link-paren-x64
- flatten-program
- resolve-predicates
- optimize-predicates
- expose-basic-blocks

## Tests

```
$ raco test $(ls *-tests.rkt)
```
