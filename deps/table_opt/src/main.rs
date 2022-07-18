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
        // Axiom U1
        rw!("if-same-fwd"; "(if ?b ?e ?e)" =>
                           "?e"),
        // XXX no reverse rule: would have to cook up a value for ?x from nothing.
        // Axiom U2
        rw!("if-flip-fwd"; "(if ?b ?e ?f)" =>
                           "(if (not ?b) ?f ?e)"),
        rw!("if-flip-rev"; "(if (not ?b) ?f ?e)" =>
                           "(if ?b ?e ?f)"),
        // Axiom U3
        rw!("if-assoc-fwd"; "(if ?c (if ?b ?e ?f) ?g)" =>
                            "(if (and ?b ?c) ?e (if ?c ?f ?g))"),
        rw!("if-assoc-rev"; "(if (and ?b ?c) ?e (if ?c ?f ?g))" =>
                            "(if ?c (if ?b ?e ?f) ?g)"),
        // Axiom U4
        rw!("test-if-fwd"; "(if ?b ?e ?f)" =>
                           "(if ?b (seq ?b ?e) ?f)"),
        rw!("test-if-rev"; "(if ?b (seq ?b ?e) ?f)" =>
                           "(if ?b ?e ?f)"),
        // Axiom U5
        rw!("distr-seq-if-rev"; "(seq (if ?b ?e ?f) ?g)" =>
                                "(if ?b (seq ?e ?g) (seq ?f ?g))"),
        rw!("distr-seq-if-fwd"; "(if ?b (seq ?e ?g) (seq ?f ?g))" =>
                                "(seq (if ?b ?e ?f) ?g)"),
        // Axiom S1
        rw!("seq-assoc-fwd"; "(seq (seq ?e ?f) ?g)" => "(seq ?e (seq ?f ?g))"),
        rw!("seq-assoc-rev"; "(seq ?e (seq ?f ?g))" => "(seq (seq ?e ?f) ?g)"),
        // Axiom S2
        rw!("seq-false-l-fwd"; "(seq false ?x)" => "false"),
        // XXX no reverse rule: would have to cook up a value for ?x from nothing.
        // Axiom S3
        rw!("seq-false-r-fwd"; "(seq ?x false)" => "false"),
        // XXX no reverse rule: would have to cook up a value for ?x from nothing.
        // Axiom S4
        rw!("seq-id-l-fwd"; "(seq nop ?x)" => "?x"),
        rw!("seq-id-l-rev"; "?x" => "(seq nop ?x)"),
        // Axiom S5
        rw!("seq-id-r-fwd"; "(seq ?x nop)" => "?x"),
        rw!("seq-id-r-rev"; "?x" => "(seq ?x nop)"),
        // Axiom S6
        // TODO: need a way of expressing that b and c are tests in order to write down the rule
        // (seq b c) => (and b c). Alternatively use the same constructor for and/seq.

        // Set and Test rules
        rw!("set-test-eq"; "(seq (set ?x ?e) (if (eq ?x ?e) ?t ?f))" =>
                           "(seq (set ?x ?e) ?t)"),
        rw!("set-test-neq"; "(seq (set ?x ?e1) (if (eq ?x ?e2) ?t ?f))" =>
                            "(seq (set ?x ?e1) ?f)"
                            if is_not_same_var(var("?e1"), var("?e2"))),
        rw!("test-comm"; "(eq ?x ?y)" => "(eq ?y ?x)"),
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
