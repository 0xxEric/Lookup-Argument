use rand::rngs::OsRng;
use std::{fmt::Debug, marker::PhantomData};

use halo2_curves::{
    bn256::{pairing, Bn256, Fr, G1Affine, G2Affine, G2Prepared, Gt, G1, G2},
    pairing::MillerLoopResult,
};

use crate::{
    backend::baloo::preprocessor::preprocess,
    pcs::{
        univariate::{
            UnivariateKzg, UnivariateKzgCommitment, UnivariateKzgParam, UnivariateKzgProverParam,
            UnivariateKzgVerifierParam,
        },
        Additive, PolynomialCommitmentScheme,
    },
    poly::univariate::UnivariatePolynomial,
    poly::Polynomial,
    util::{
        arithmetic::{barycentric_weights, root_of_unity, variable_base_msm, Field, PrimeField},
        test::std_rng,
        transcript::{InMemoryTranscript, Keccak256Transcript, TranscriptRead, TranscriptWrite},
    },
};

pub mod preprocessor;
pub mod prover;
pub mod util;
pub mod verifier;

use prover::Prover;
use verifier::Verifier;

use super::*;
use crate::util::transcript::{
    FieldTranscriptRead, FieldTranscriptWrite, G2TranscriptRead, G2TranscriptWrite,
};
type Pcs = UnivariateKzg<Bn256>;
use std::cmp::max;

use std::time::Instant;

pub fn test_baloo_by_input(table:Vec<Fr>,lookup:Vec<Fr>,)->Vec<String> {
    let mut timings: Vec<String> = vec![];
    let m = lookup.len();
        let t = table.len();
        let poly_size = max(t, m).next_power_of_two() * 2;
        let d = poly_size - 2;

        // 1. setup
        let start = Instant::now();
        let (param, pp, vp) = preprocess(t, m).unwrap();
        assert_eq!(poly_size, 2_usize.pow(pp.k() as u32));
        let duration = start.elapsed();
        timings.push(format!(
            "setup and preprocess: k=, {}ms",
            duration.as_millis()
        ));
        println!(
            "------------?Setup and preprocess: {}ms-----------",
            duration.as_millis()
        );

        // 2. generate proof
        let start = Instant::now();
        let prover = Prover::new(&table, &param, &pp);
        let proof = prover.prove(&lookup);
        let duration = start.elapsed();
        timings.push(format!("prove: k=, {}ms", duration.as_millis()));
        println!("------------prove: {}ms------------", duration.as_millis());
        println!("proof: {:?}", proof);

        let scalar_0 = Fr::from(0 as u64);
        let scalar_1 = Fr::from(1 as u64);

        // 3.1 prepare for verifier
        // z_h(x) = X^t - 1, [-1, 0, ..., 0, 1], t-1 0s in between
        let z_h_poly_coeffs = vec![scalar_1.neg()]
            .into_iter()
            .chain(vec![scalar_0; t - 1])
            .chain(vec![scalar_1])
            .collect();
        let z_h_poly = UnivariatePolynomial::monomial(z_h_poly_coeffs);
        // [z_h(x)]1
        let z_h_comm_1 = Pcs::commit_monomial(&pp, &z_h_poly.coeffs());
        // t(x)
        let t_poly = UnivariatePolynomial::lagrange(table.clone()).ifft();
        // [t(x)]1
        let t_comm_1 = Pcs::commit_monomial(&pp, &t_poly.coeffs());

        // φ(x)
        let phi_poly = UnivariatePolynomial::lagrange(lookup.clone()).ifft();
        let phi_comm_1 = Pcs::commit_monomial(&pp, &phi_poly.coeffs());
        // todo: cached all [x^s]1, [x^s]2?
        // X^m
        let x_m_exponent_poly = UnivariatePolynomial::monomial(
            vec![scalar_0; m]
                .into_iter()
                .chain(vec![scalar_1])
                .collect(),
        );
        // [X^m]1
        let x_m_exponent_poly_comm_1 =
            Pcs::commit_monomial(&pp, &x_m_exponent_poly.clone().coeffs());

        // X^(d-m+1)
        let coeffs_x_exponent_poly = vec![scalar_0; d - m + 1]
            .into_iter()
            .chain(vec![scalar_1])
            .collect();
        let x_exponent_poly = UnivariatePolynomial::monomial(coeffs_x_exponent_poly);
        // [X^(d-m+1)]2
        let x_exponent_poly_comm_2 = Pcs::commit_monomial_g2(&param, &x_exponent_poly.coeffs());
        println!("x_exponent_poly_comm_2: {:?}", x_exponent_poly_comm_2);

        // X^(d-m+2)
        let coeffs_x_exponent_poly_2 = vec![scalar_0; d - m + 2]
            .into_iter()
            .chain(vec![scalar_1])
            .collect();
        let x_exponent_poly_2 = UnivariatePolynomial::monomial(coeffs_x_exponent_poly_2);
        // [X^(d-m+2)]1
        let x_exponent_poly_2_comm_1 = Pcs::commit_monomial(&pp, &x_exponent_poly_2.coeffs());
        // [X^(d-m+2)]2
        let x_exponent_poly_2_comm_2 = Pcs::commit_monomial_g2(&param, &x_exponent_poly_2.coeffs());

        // 3.2 verifier to verify
        let start = Instant::now();
        let verifier = Verifier::new(&vp);
        verifier.verify(
            &proof,
            &t_comm_1,
            &z_h_comm_1,
            &phi_comm_1,
            &x_m_exponent_poly_comm_1,
            &x_exponent_poly_comm_2,
            &x_exponent_poly_2_comm_1,
            &x_exponent_poly_2_comm_2,
            m,
        );
        let duration = start.elapsed();
        timings.push(format!("verify: k=, {}ms", duration.as_millis()));
        println!("------------verify: {}ms------------", duration.as_millis());
        println!("Finished to verify: baloo");
        timings
}

pub fn test_baloo_by_k(k:usize)->Vec<String> {
    let mut timings: Vec<String> = vec![];
    timings
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::util::transcript::{
        FieldTranscriptRead, FieldTranscriptWrite, G2TranscriptRead, G2TranscriptWrite,
    };
    use halo2_curves::bn256::Fr;
    type Pcs = UnivariateKzg<Bn256>;
    use std::cmp::max;
    #[test]
    pub fn test_baloo(k:usize)->Vec<String> {
        let mut timings: Vec<String> = vec![];
        
        let table = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(4),
            Fr::from(5),
            Fr::from(6),
            Fr::from(7),
            Fr::from(8),
        ];
        let lookup = vec![Fr::from(4), Fr::from(3), Fr::from(5), Fr::from(2)];

        let m = lookup.len();
        let t = table.len();
        let poly_size = max(t, m).next_power_of_two() * 2;
        let d = poly_size - 2;

        // 1. setup
        let start = Instant::now();
        let (param, pp, vp) = preprocess(t, m).unwrap();
        assert_eq!(poly_size, 2_usize.pow(pp.k() as u32));
        let duration = start.elapsed();
        timings.push(format!(
            "setup and preprocess: k=, {}ms",
            duration.as_millis()
        ));
        println!(
            "------------?Setup and preprocess: {}ms-----------",
            duration.as_millis()
        );

        // 2. generate proof
        let start = Instant::now();
        let prover = Prover::new(&table, &param, &pp);
        let proof = prover.prove(&lookup);
        let duration = start.elapsed();
        timings.push(format!("prove: k=, {}ms", duration.as_millis()));
        println!("------------prove: {}ms------------", duration.as_millis());
        println!("proof: {:?}", proof);

        let scalar_0 = Fr::from(0 as u64);
        let scalar_1 = Fr::from(1 as u64);

        // 3.1 prepare for verifier
        // z_h(x) = X^t - 1, [-1, 0, ..., 0, 1], t-1 0s in between
        let z_h_poly_coeffs = vec![scalar_1.neg()]
            .into_iter()
            .chain(vec![scalar_0; t - 1])
            .chain(vec![scalar_1])
            .collect();
        let z_h_poly = UnivariatePolynomial::monomial(z_h_poly_coeffs);
        // [z_h(x)]1
        let z_h_comm_1 = Pcs::commit_monomial(&pp, &z_h_poly.coeffs());
        // t(x)
        let t_poly = UnivariatePolynomial::lagrange(table.clone()).ifft();
        // [t(x)]1
        let t_comm_1 = Pcs::commit_monomial(&pp, &t_poly.coeffs());

        // φ(x)
        let phi_poly = UnivariatePolynomial::lagrange(lookup.clone()).ifft();
        let phi_comm_1 = Pcs::commit_monomial(&pp, &phi_poly.coeffs());
        // todo: cached all [x^s]1, [x^s]2?
        // X^m
        let x_m_exponent_poly = UnivariatePolynomial::monomial(
            vec![scalar_0; m]
                .into_iter()
                .chain(vec![scalar_1])
                .collect(),
        );
        // [X^m]1
        let x_m_exponent_poly_comm_1 =
            Pcs::commit_monomial(&pp, &x_m_exponent_poly.clone().coeffs());

        // X^(d-m+1)
        let coeffs_x_exponent_poly = vec![scalar_0; d - m + 1]
            .into_iter()
            .chain(vec![scalar_1])
            .collect();
        let x_exponent_poly = UnivariatePolynomial::monomial(coeffs_x_exponent_poly);
        // [X^(d-m+1)]2
        let x_exponent_poly_comm_2 = Pcs::commit_monomial_g2(&param, &x_exponent_poly.coeffs());
        println!("x_exponent_poly_comm_2: {:?}", x_exponent_poly_comm_2);

        // X^(d-m+2)
        let coeffs_x_exponent_poly_2 = vec![scalar_0; d - m + 2]
            .into_iter()
            .chain(vec![scalar_1])
            .collect();
        let x_exponent_poly_2 = UnivariatePolynomial::monomial(coeffs_x_exponent_poly_2);
        // [X^(d-m+2)]1
        let x_exponent_poly_2_comm_1 = Pcs::commit_monomial(&pp, &x_exponent_poly_2.coeffs());
        // [X^(d-m+2)]2
        let x_exponent_poly_2_comm_2 = Pcs::commit_monomial_g2(&param, &x_exponent_poly_2.coeffs());

        // 3.2 verifier to verify
        let start = Instant::now();
        let verifier = Verifier::new(&vp);
        verifier.verify(
            &proof,
            &t_comm_1,
            &z_h_comm_1,
            &phi_comm_1,
            &x_m_exponent_poly_comm_1,
            &x_exponent_poly_comm_2,
            &x_exponent_poly_2_comm_1,
            &x_exponent_poly_2_comm_2,
            m,
        );
        let duration = start.elapsed();
        timings.push(format!("verify: k=, {}ms", duration.as_millis()));
        println!("------------verify: {}ms------------", duration.as_millis());
        println!("Finished to verify: baloo");
        timings
    }
}
