use std::{marker::PhantomData};


use halo2_proofs::{
    circuit::{ AssignedCell, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{self, Advice, Circuit, Column, ConstraintSystem, Error, Selector, Fixed},
    poly::Rotation
};

use ff::{Field, PrimeField};



/* -----------              MUL             ----------------- */

// STEP 1:    First Write Your TestStruct
struct MulCircuit<F: Field> {

    _ph: PhantomData<F>,

    secret: Value<F>,
}

// Testing Equality Constraints Bug
struct MaliciousCircuit<F: Field> {
    
    _ph: PhantomData<F>,

    value1: Value<F>,

    value2: Value<F>,
}

// STEP 2:  Write Your Config for The Struct
#[derive(Clone, Debug)]

struct MulConfig<F: Field + Clone> {

    q_mul_enable: Selector,

    q_add_enable: Selector,

    q_fixed_enable: Selector,

    advice: Column<Advice>,

    fixed: Column<Fixed>,

    _ph: PhantomData<F>,
}


// STEP 3: Implement the Circuit Struct and its methods on my MulStruct
impl<F: PrimeField> Circuit<F> for MulCircuit<F> {

    // I == Define your types for the config and the intended layout (SimpleFloorPlanner)
    type Config = MulConfig<F>;

    type FloorPlanner = SimpleFloorPlanner;

    // II  == Implement the 3 basic methods of Circuit<F> for your MulStruct:, without_witnesses, configure and synthesis
    fn without_witnesses(&self) -> Self {
        
        MulCircuit {
            _ph: PhantomData,

            secret: Value::unknown()
        }
    }


    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        
        // a) Add 2 Columns to the circuit: 2 Selectors and Advice Columns
        let q_mul_enable = meta.complex_selector();
        let q_add_enable = meta.complex_selector();

        let q_fixed_enable = meta.complex_selector();


        let advice = meta.advice_column();
        // Add Fixed Column
        let fixed = meta.fixed_column();

        // To Enforce Equality Constraints, we need to enable equality constraints
        // on that specified column ( in this case, the advice column), and then enforce 
        //equality on the cells during the advice assignment
        meta.enable_equality(advice);

        // Enable Equality For The Fixed Column as well
        meta.enable_constant(fixed);

        // b) Define a new Gate
        meta.create_gate("vertical-mul", |meta| {
            // Set the constraints
            let w0 = meta.query_advice(advice, Rotation(0));// Rotation(0) = Rotation::cur()
            let w1 = meta.query_advice(advice, Rotation(1));// Rotation(1) = Rotation::next()
            let w2 = meta.query_advice(advice, Rotation(2));// Rotation(2) = The Next Next row

            let q_mul_enable = meta.query_selector(q_mul_enable);// Setting Up The Selector Column to Control the Gates

            // Constraint Enforcer
            vec![q_mul_enable * (w0 * w1 - w2)]
        });

        // b) Define Addition Gate
        meta.create_gate("vertical-add", |meta| {
            let w0 = meta.query_advice(advice, Rotation(0));
            let w1 = meta.query_advice(advice, Rotation(1));
            let w2 = meta.query_advice(advice, Rotation(2));

            let q_add_enable = meta.query_selector(q_add_enable);

            // Add Constraint Enforcer
            vec![q_add_enable * (w0 + w1 - w2)]
        });

        // c) Define a New Gate For The Fixed Column That Checks A Cell Against A Constant
        meta.create_gate("fixed equal-constant check", |meta| {
            let w0 = meta.query_advice(advice, Rotation::cur());
            let c1 = meta.query_fixed(fixed, Rotation::cur());
            let q_fixed_enable = meta.query_selector(q_fixed_enable);

            // Add Constraint Enforcer
            vec!(q_fixed_enable * (w0 - c1))
        });

        // Function Returns = the Config struct
        MulConfig {
            q_mul_enable,

            q_add_enable,

            q_fixed_enable,

            advice,

            fixed,

            _ph: PhantomData
        }
    }

    #[allow(unused_variables)]
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), plonk::Error> {

        // Create A New Free Variable by calling the function (unconstrained)
        let free_variable_1 = MulCircuit::<F>::unconstrained(
            &config,
            &mut layouter,
            self.secret.clone(),
        )?;

        // Do A Few Multiplications
        let free_variable_2 = MulCircuit::<F>::mul(
            &config,
            &mut layouter,
            free_variable_1.clone(),
            free_variable_1.clone(),
        )?;

        let free_variable_3 = MulCircuit::<F>::mul(
            &config,
            &mut layouter,
            free_variable_2.clone(),
            free_variable_1.clone(),
        )?;

        let free_variable_5 = MulCircuit::<F>::mul(
            &config,
            &mut layouter,
            free_variable_3.clone(),
            free_variable_2.clone(),
        )?;

        // Do A Few Addition synthesis
        let free_add_var_2 = MulCircuit::<F>::add(
            &config,
            &mut layouter,
            free_variable_1.clone(),
            free_variable_1.clone(),
        )?;

        let free_add_var_3 = MulCircuit::<F>::add(
            &config,
            &mut layouter,
            free_add_var_2.clone(),
            free_variable_1.clone(),
        )?;

        let free_add_var_5 = MulCircuit::<F>::add(
            &config,
            &mut layouter,
            free_add_var_3.clone(),
            free_add_var_2.clone(),
        )?;

        // Bring In The Fixed Constant implementation here
        MulCircuit::<F>::fixed(
            &config,
            &mut layouter,
            F::from_u128(4272253717090457),
            free_variable_5
        )?;
        
        Ok(())
    }
}


// OPTIONAL STEP:    Let's implement Some Other methods To Be Called In The Synthesize
impl<F: PrimeField> MulCircuit<F> {

    // This region occupies 3 rows
    #[allow(unused_variables)]
    fn mul(
        config: &<Self as Circuit<F>>::Config,
        layouter: &mut impl Layouter<F>,
        lhs: AssignedCell<F, F>,
        rhs: AssignedCell<F, F>,

    ) -> Result<AssignedCell<F, F>, plonk::Error> {

        // Assign Region
        layouter.assign_region(
            || "mul",
            |mut region| {
                //
                let v0 = lhs.value().cloned();
                let v1 = rhs.value().cloned();

                let v2 = v0
                    .and_then(|v0| v1.and_then(|v1| Value::known(v0 * v1)));

                let w0 = region.assign_advice(
                    || "assign w0",
                    config.advice,
                    0,
                    || v0,
                )?;

                let w1 = region.assign_advice(
                    || "assign w1",
                    config.advice,
                    1,
                    || v1,
                )?;

                let w2 = region.assign_advice(
                    || "assign w2",
                    config.advice,
                    2,
                    || v2,
                )?;

                // b) Turn ON The Gate
                config.q_mul_enable.enable(&mut region, 0)?;

                // Introduce Equality Enforcements Here : Ensure constraining The correct cells
                region.constrain_equal(w0.cell(), lhs.cell())?;
                region.constrain_equal(w1.cell(), rhs.cell())?;
                Ok(w2)
            },
        )
    }

    // Implements an Addition Gate
    #[allow(unused_variables)]
    fn add(
        config: &<Self as Circuit<F>>::Config,
        layouter: &mut impl Layouter<F>,
        lhs: AssignedCell<F, F>,
        rhs: AssignedCell<F, F>
    ) -> Result<AssignedCell<F, F>, plonk::Error> {
        // Assign Region
        layouter.assign_region(
            || "add", | mut region | {
                // Assign The Input values
                let value0 = lhs.value().cloned();
                let value1 = rhs.value().cloned();

                let value2 = value0
                    .and_then(|value0 | value1.and_then(|value1| Value::known(value0 + value1)));

                let z0 = region.assign_advice(
                    ||"assign z0",
                    config.advice,
                    0,
                    || value0
                )?;

                let z1 = region.assign_advice(
                    || "assign z1",
                    config.advice,
                    1,
                    ||value1,
                )?;

                let z2 = region.assign_advice(
                    ||"assign z2",
                    config.advice,
                    2,
                    || value2,
                )?;

                // Turn On The Gate
                config.q_add_enable.enable(&mut region, 0)?;
                Ok(z2)
            }
        )
    }

    // Implement A Single Approach To Assigning and Enforcing Equality Constraints
    #[rustfmt::skip]
    fn mul_sugar(
        config: &<Self as Circuit<F>>::Config,
        layouter: &mut impl Layouter<F>,
        lhs: AssignedCell<F, F>,
        rhs: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {

        layouter.assign_region(
            ||"mul-sugar",
            |mut region| {
                let w0 = lhs.value().cloned();
                let w1 = rhs.value().cloned();
                let w2 = 
                    w0
                        .and_then(|w0|w1.and_then(|w1| Value::known(w0 * w1)));

                // Copy And Enforce Equality Constraints Between w0/w1 cells and lhs/rhs cells
                let _w0 = lhs.copy_advice(
                    ||"assign w0", &mut region, config.advice, 0
                )?;
                let _w1 = rhs.copy_advice(
                    ||"assign w1", &mut region, config.advice, 1
                )?;
                let w2 = region.assign_advice(
                    ||"assign w2", config.advice, 2, ||w2
                )?;

                config.q_mul_enable.enable(&mut region, 0)?;
                // ANCHOR_END: copy
                
                Ok(w2)
            }
        )
    }

    fn fixed(
        config: &<Self as Circuit<F>>::Config,
        layouter: &mut impl Layouter<F>,
        value: F,
        variable: AssignedCell<F, F>,
    ) -> Result<(), Error> {

        layouter.assign_region(
            || "fixed",
            |mut region| {
                variable.copy_advice(
                    ||"assign variable",
                    &mut region,
                    config.advice,
                    0,
                )?;
                let fixed_cell = region.assign_fixed(
                    || "assign constant",
                    config.fixed,
                    0,
                    || Value::known(value),
                )?;

                // Turn The Fixed Gate On
                config.q_fixed_enable.enable(&mut region, 0)?;

                // Equality Constraints On Fixed Cell Below:
                region.constrain_equal(variable.cell(), fixed_cell.cell())?;
                Ok(())
            }
        )
    }

    // To Use the Mul function, we will need some way to create assigned cells. 
    // Create a function which allocates a small region (1 row), enables no gates
    // and simply returns the cell
    fn unconstrained(
        config: &<Self as Circuit<F>>::Config,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {

        layouter.assign_region(
            || "free-variable",
            |mut region| {
                region.assign_advice(
                    || "assign w0",
                    config.advice,
                    0,
                    || value,
                )
            },
        )
    }

}

// Implement Circuit Methods For Malicious Circuit
impl<F: PrimeField> Circuit<F> for MaliciousCircuit<F> {

    type Config = MulConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        MaliciousCircuit {
            _ph: PhantomData,
            value1: Value::unknown(),
            value2: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        
        MulCircuit::<F>::configure(meta)
    }

    #[allow(unused_variables)]
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        
        // Create legitimate Input
        let mal_input_1 = MulCircuit::<F>::unconstrained(
            &config,
            &mut layouter,
            self.value1.clone(),
        )?;

        // Now Craft Malicious Input instead of using the Mul function
        let mal_input_2 = MulCircuit::<F>::unconstrained(
            &config,
            &mut layouter,
            self.value2.clone(),
        )?;

        let mal_result = MulCircuit::<F>::mul(
            &config,
            &mut layouter,
            mal_input_1,
            mal_input_2,
        )?;

        Ok(())
    }
}






fn main() {

    use halo2_proofs::halo2curves::bn256::Fr;

    let known_value = Fr::from(5u64);

    let _halo_circuit = MulCircuit::<Fr> {_ph: PhantomData, secret: Value::known(known_value) };

    // Exploiting the Non-Equality Constraint Bug
    let malicious_circuit = MaliciousCircuit::<Fr> {
        _ph: PhantomData,
        value1: Value::known(Fr::from(5u64)),
        value2: Value::known(Fr::from(10u64)),
    };

    let halo_prover = MockProver::run(8, &malicious_circuit, vec![]).unwrap();

    match halo_prover.verify() {
        Ok(_) => println!("Verification Successful!"),
        Err(e) => println!("Verification Failed!: {:?} ", e),
    }
}
