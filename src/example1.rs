use halo2_proofs::{
    arithmetic::Field, circuit::*, dev::MockProver, pasta::Fp, plonk::*, poly::Rotation,
};
use std::marker::PhantomData;

/// config of circuit defines the number of columns
#[derive(Clone, Debug)]
struct FiboConfig {
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
}

struct FiboChip<F: Field> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

// want to reuse this Assigned Cell type
#[derive(Clone, Debug)]
struct ACell<F: Field>(AssignedCell<F, F>);

impl<F: Field> FiboChip<F> {
    /// base on config, construct the chip
    fn construct(config: FiboConfig) -> Self {
        FiboChip {
            config,
            _marker: PhantomData,
        }
    }

    /// base on constraint system, return configure the chip
    fn configure(meta: &mut ConstraintSystem<F>) -> FiboConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector_column = meta.selector();

        // 0. This enables permutation check
        // need to copy the sequences to next raw (= using permutation argument)
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);

        meta.create_gate("add", |meta| {
            // 1. Query cells from columns
            // | col_a | col_b | col_c | selector |
            // |   a   |   b   |   c   |     s    |
            let s = meta.query_selector(selector_column);
            // note: rotation is offset of the row compared from selector location / rotation cause the cost
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            // 2. Return the constraint
            // a + b = c as a constraint in this case ( only when the selector,s, is true )
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice: [col_a, col_b, col_c],
            selector: selector_column,
        }
    }

    fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: Option<F>,
        b: Option<F>,
    ) -> Result<(ACell<F>, ACell<F>, ACell<F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                // 1. Enable the selector (= I will enable constraint of the first row)
                self.config.selector.enable(&mut region, 0)?;

                // 2. assign the two private value a,b to the cell
                let a_cell = region
                    .assign_advice(
                        || "a",
                        self.config.advice[0],
                        0,
                        || Value::known(a.unwrap()),
                    )
                    .map(ACell)?;

                let b_cell = region
                    .assign_advice(
                        || "b",
                        self.config.advice[1],
                        0,
                        || Value::known(b.unwrap()),
                    )
                    .map(ACell)?;

                // c value is a + b
                let c_val = a.and_then(|a| b.map(|b| a + b));
                let c_cell = region
                    .assign_advice(
                        || "c",
                        self.config.advice[2],
                        0,
                        || Value::known(c_val.unwrap()),
                    )
                    .map(ACell)?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &ACell<F>,
        prev_c: &ACell<F>,
    ) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                // copy constraint
                prev_b
                    .0
                    .copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;
                prev_c
                    .0
                    .copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;

                // c value is a + b
                let c_val = prev_b
                    .0
                    .value()
                    .and_then(|b| prev_c.0.value().map(|c| *b + *c));
                let c_cell = region
                    .assign_advice(|| "c", self.config.advice[2], 0, || c_val)
                    .map(ACell)?;

                Ok(c_cell)
            },
        )
    }
}

#[derive(Debug)]
struct FiboCircuit<F> {
    pub a: Option<F>,
    pub b: Option<F>,
}

impl<F: Field> Circuit<F> for FiboCircuit<F> {
    // you could have custom config for circuit
    type Config = FiboConfig;
    // this is the one who decide layout of regions
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        // TODO: halo_proof v0.3.0 doesn't have default option
        Self { a: None, b: None }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // note: In this case, you defining columns inside the circuit
        // but if you define columns in this circuit configure
        // you could decide coulmns to `reuse` in multiple chips
        FiboChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // get actual Fibo chip instance
        let fibo_chip = FiboChip::construct(config);

        // we assigned values to first row
        let (_, mut prev_b, mut prev_c) =
            fibo_chip.assign_first_row(layouter.namespace(|| "first row"), self.a, self.b)?;

        for _i in 3..10 {
            let c = fibo_chip.assign_row(layouter.namespace(|| "next row"), &prev_b, &prev_c)?;

            // update the base cell value
            prev_b = prev_c;
            prev_c = c;
        }
        Ok(())
    }
}

fn main() {
    // k is size of circuit
    let k = 4;

    let a = Fp::from(1);
    let b = Fp::from(1);
    let fibo_circuit = FiboCircuit {
        a: Some(a),
        b: Some(b),
    };

    let prover = MockProver::run(k, &fibo_circuit, vec![]).unwrap();
    prover.assert_satisfied()
}
