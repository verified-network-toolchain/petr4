use egg::{*};

define_language! {
    pub enum TableLang {
        Bool(bool),
        "if"  = If([Id; 3]),
        "and" = And([Id; 2]),
        "not" = Not(Id),
        "seq" = Seq([Id; 2]),
        "nop" = Nop,
        "set" = Set([Id; 2]),
        "eq"  = Eq([Id; 2]),
        Symbol(Symbol),
    }
}
