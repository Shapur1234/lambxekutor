use clap::{ArgAction::SetTrue, Parser, ValueEnum};
use lambxekutor_lib::{
    evaluation::{ApplicativeEvaluation, Evaluation, NormalEvaluation},
    expression::{Lambda, RawLambda},
};

#[derive(Clone, Debug, ValueEnum)]
enum EvaluationStrategy {
    Normal,
    Applicative,
}

#[derive(Clone, Debug, Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[arg(
        short,
        long,
        action = SetTrue,
        default_value_t = false,
        help = "Show intermediate evaluation steps"
    )]
    show_intermediate_steps: bool,

    #[arg(short, long, value_enum, default_value_t = EvaluationStrategy::Normal, help = "Choose evaluation strategy")]
    evaluation_strategy: EvaluationStrategy,

    expression: String,
}

fn main() {
    let cli = Cli::parse();
    match TryInto::<RawLambda>::try_into(cli.expression.as_ref()) {
        Ok(raw_lambda) => {
            println!("Result of parsing: '{raw_lambda}'");

            let (mut lambda, mut context) = Lambda::desugar(&raw_lambda);
            println!("Result of desugaring: '{}'", context.bind(&lambda));

            if cli.show_intermediate_steps {
                println!("Evaluation steps:");
                match cli.evaluation_strategy {
                    EvaluationStrategy::Normal => {
                        for (index, step) in NormalEvaluation::from(lambda).enumerate() {
                            println!("{}. '{}'", index + 1, context.bind(&step));
                        }
                    }
                    EvaluationStrategy::Applicative => {
                        for (index, step) in ApplicativeEvaluation::from(lambda).enumerate() {
                            println!("{}. '{}'", index + 1, context.bind(&step));
                        }
                    }
                }
            } else {
                match cli.evaluation_strategy {
                    EvaluationStrategy::Normal => NormalEvaluation::evaluate(&mut lambda),
                    EvaluationStrategy::Applicative => ApplicativeEvaluation::evaluate(&mut lambda),
                }
                println!("Result of evaluation: {}", context.bind(&lambda));
            }
        }
        Err(errors) => {
            eprintln!("Falied to parse expression");
            for error in errors {
                eprintln!("{error}");
            }
        }
    }
}

