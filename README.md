# Lambda expression evaluator

## Features

- Supports multivariable lambda expressions, normal and applicative execution
- Also supports the following macros
  - `AND := (λ x y . x y x)`
  - `F := (λ t f . f)`
  - `NOT := (λ x t f . x f t)`
  - `OR := (λ x y . x T y)`
  - `PRED := (λ x s z . x (λ f g . g (f s)) (λ g . z) (λ u . u))`
  - `SUC := (λ n s z . s (n s z))`
  - `T := (λ t f . t)`
  - `Y := (λ f . (λ x . f (x x)) (λ x . f (x x)))`
  - `ZERO := (λ n . n (λ x . (λ t f . f)) (λ t f . t))`
  - `< := (λ m n . > n m )`
  - `> := (λ m n . NOT (ZERO (- m n)))`
  - `- := (λ m n . (n PRED) m)`
  - `= := (λ m n . ZERO (DELTA m n))`
  - `<= := (λ m n . ZERO (- m n))`
  - `>= := (λ m n . ZERO (- n m))`
  - `/ := (λ n . Y (λ c n m f x . (λ d . ZERO d (0 f x) (f (c d m f x))) (- n m)) (SUC n))`
  - `* := (λ x y s . x (y s))`
  - `+ := (λ x y s z . x s (y s z))`
  - `^ := (λ x y . y x)`

## Example usage

- Build directly with `cargo build --release` or use `nix build .#`
- `nix run .# -- --help`
- `nix run .# -- 'Y (λf n. ZERO n 1 (* n (f (- n 1)))) 4'`
- `nix run .# -- -s 'Y (λf n. ZERO n 1 (* n (f (- n 1)))) 4'`
- `nix run .# -- --show-intermediate-steps --evaluation-strategy=applicative 'Y (λf n. ZERO n 1 (* n (f (- n 1)))) 0'`
