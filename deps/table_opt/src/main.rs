use egg::{*, rewrite as rw};

// From https://github.com/egraphs-good/egg/blob/main/tests/lambda.rs
fn var(s: &str) -> Var {
    s.parse().unwrap()
}

// From https://github.com/egraphs-good/egg/blob/main/tests/lambda.rs
fn is_not_same_var(v1: Var, v2: Var) -> impl Fn(&mut EGraph<SymbolLang, ()>, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph.find(subst[v1]) != egraph.find(subst[v2])
}

fn run(rules: &[Rewrite<SymbolLang, ()>], orig_str: &str) {
    let orig_expr = orig_str.parse().unwrap();
    let runner = Runner::default().with_expr(&orig_expr).run(rules);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    print!("orig: {}\nbest: {}\ncost: {}\n\n", orig_expr, best_expr, best_cost);
}

fn main() {
    let rules: &[Rewrite<SymbolLang, ()>] = &[
        rw!("if-same"; "(if ?b ?x ?x)" =>
                       "?x"),
        rw!("distr-seq-if"; "(seq (if ?b ?x ?y) ?z)" =>
                            "(if ?b (seq ?x ?z) (seq ?y ?z))"),
        rw!("distr-seq-if-rev"; "(if ?b (seq ?x ?z) (seq ?y ?z))" =>
                                "(seq (if ?b ?x ?y) ?z)"),
        rw!("set-test-eq"; "(seq (set ?x ?e) (if (eq ?x ?e) ?t ?f))" =>
                           "(seq (set ?x ?e) ?t)"),
        rw!("set-test-neq"; "(seq (set ?x ?e1) (if (eq ?x ?e2) ?t ?f))" =>
                            "(seq (set ?x ?e1) ?f)"
                            if is_not_same_var(var("?e1"), var("?e2"))),
        rw!("test-comm"; "(eq ?x ?y)" => "(eq ?y ?x)"),
        rw!("seq-id-l"; "(seq nop ?x)" => "?x"),
        rw!("seq-id-r"; "(seq ?x nop)" => "?x"),
    ];

    run(rules, "(seq
                   (if (eq ip 10.0.0.1)
                       (set eth aa:bb:cc:dd:ee:ff)
                       (set eth aa:aa:aa:aa:aa:aa))
                   (if (eq eth aa:bb:cc:dd:ee:ff)
                       (set port 1)
                       (set port 2)))");

    run(rules, "(seq
                   (if cond1 (set eth A)
                             (if cond2
                                 (set eth C)
                                 (set eth D)))
                   (if (eq eth B)
                       (set port 1)
                       (set port 2)))");

    run(rules, "(seq
                   (if (eq ip 10.0.0.1)
                       (set eth A)
                       (if (eq ip 10.0.0.2)
                           (set eth B)
                           (set eth F)))
                   (if (eq eth A)
                       (set port 1)
                       (set port 2)))");

    let bad_rules: &[Rewrite<SymbolLang, ()>] = &[
        rw!("expand"; "(f ?x)" =>
                      "(+ (f ?x) (f ?x))"),
    ];

    run(bad_rules, "(f a)");

}
