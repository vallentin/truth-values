#[derive(PartialEq, Debug)]
enum Expr {
    Bool(bool),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
}

impl Expr {
    fn eval(&self) -> bool {
        match self {
            &Self::Bool(b) => b,
            Self::And(lhs, rhs) => lhs.eval() && rhs.eval(),
            Self::Or(lhs, rhs) => lhs.eval() || rhs.eval(),
            Self::Not(operand) => !operand.eval(),
        }
    }
}

fn and(lhs: impl Into<Expr>, rhs: impl Into<Expr>) -> Expr {
    Expr::And(Box::new(lhs.into()), Box::new(rhs.into()))
}

fn or(lhs: impl Into<Expr>, rhs: impl Into<Expr>) -> Expr {
    Expr::Or(Box::new(lhs.into()), Box::new(rhs.into()))
}

fn not(operand: impl Into<Expr>) -> Expr {
    Expr::Not(Box::new(operand.into()))
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

fn main() {
    truth_values::each_const(|[a, b]| {
        assert_eq!(!(a || b), !a && !b);
        assert_eq!(!(a && b), !a || !b);
    });

    let mut exprs = Vec::new();
    exprs.extend(truth_values::gen_const().map(|[a, b]| {
        let x = not(or(a, b));
        let y = and(not(a), not(b));
        (x, y)
    }));
    exprs.extend(truth_values::gen_const().map(|[a, b]| {
        let x = not(and(a, b));
        let y = or(not(a), not(b));
        (x, y)
    }));

    for (x, y) in exprs {
        println!("{} = {:?}", x.eval(), x);
        println!("{} = {:?}", y.eval(), y);
        println!();

        assert_eq!(x.eval(), y.eval());
    }
}
