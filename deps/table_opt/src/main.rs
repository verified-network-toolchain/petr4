use egg::{*, rewrite as rw};

fn main() {
    let rules: &[Rewrite<SymbolLang, ()>] = &[
        rw!("if-same"; "(if ?b ?x ?x)" => "?x"),
        rw!("distr-seq-if"; "(seq (if ?b ?x ?y) ?z)" => "(if ?b (seq ?x ?z) (seq ?y ?z))"),
        rw!("set-test-eq"; "(seq (set ?x ?e) (if (eq ?x ?e) ?t ?f))" => "(seq (set ?x ?e) ?t)"),
        //rw!("set-test-neq"; "(seq (set ?x ?e1) (if (eq ?x ?e2) ?t ?f))" =>
        //    "(seq (set ?x ?e1) ?f)"
        //if ConditionEqual::parse("?e1", "?e2")),
        rw!("test-comm"; "(eq ?x ?y)" => "(eq ?y ?x)"),
        rw!("seq-id-l"; "(seq nop ?x)" => "?x"),
        rw!("seq-id-r"; "(seq ?x nop)" => "?x"),
    ];

    // While it may look like we are working with numbers,
    // SymbolLang stores everything as strings.
    // We can make our own Language later to work with other types.
    let start =
"
(seq
  (if (eq ip 10.0.0.1)
      (set eth aa:bb:cc:dd:ee:ff)
      (set eth aa:aa:aa:aa:aa:aa))
  (if (eq eth aa:bb:cc:dd:ee:ff)
      (set port 2)
      (set port 1)))
".parse().unwrap();

    // That's it! We can run equality saturation now.
    let runner = Runner::default().with_expr(&start).run(rules);

    // Extractors can take a user-defined cost function,
    // we'll use the egg-provided AstSize for now
    let extractor = Extractor::new(&runner.egraph, AstSize);

    // We want to extract the best expression represented in the
    // same e-class as our initial expression, not from the whole e-graph.
    // Luckily the runner stores the eclass Id where we put the initial expression.
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    println!("best expression: {}\ncost: {}", best_expr, best_cost);
}
