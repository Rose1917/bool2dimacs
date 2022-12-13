#### What is this
an end-to-end cnf parser.

#### Usage
```rust
use bool2cnf::parse_dimacs
    fn test_parse(){
        let input = "A&&(B||!(D&&E))";
        println!("raw string:{}", input);
        let p = parse_dimacs(input);
        println!("dimacs:\n{}", p);
    }

```

#### Todo
- [ ] Added customized operator
- [ ] An optional sat-solver

