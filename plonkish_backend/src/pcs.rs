use crate::{
    util::{
        arithmetic::Field,
        transcript::{TranscriptRead, TranscriptWrite},
    },
    Error,
};
use rand::RngCore;
use std::fmt::Debug;

pub mod multilinear;
pub mod univariate;

pub trait PolynomialCommitmentScheme<F: Field>: Clone + Debug {
    type Param: Debug;
    type ProverParam: Debug;
    type VerifierParam: Debug;
    type Polynomial: Debug;
    type Point: Debug;
    type Commitment: Clone + Debug + Default;
    type CommitmentWithAux: Debug + Default + AsRef<Self::Commitment>;

    fn setup(size: usize, rng: impl RngCore) -> Result<Self::Param, Error>;

    fn trim(
        param: &Self::Param,
        size: usize,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error>;

    fn commit(
        pp: &Self::ProverParam,
        poly: &Self::Polynomial,
    ) -> Result<Self::CommitmentWithAux, Error>;

    fn commit_and_write(
        pp: &Self::ProverParam,
        poly: &Self::Polynomial,
        transcript: &mut impl TranscriptWrite<Self::Commitment, F>,
    ) -> Result<Self::CommitmentWithAux, Error> {
        let comm = Self::commit(pp, poly)?;
        transcript.write_commitment(comm.as_ref())?;
        Ok(comm)
    }

    fn batch_commit<'a>(
        pp: &Self::ProverParam,
        polys: impl IntoIterator<Item = &'a Self::Polynomial>,
    ) -> Result<Vec<Self::CommitmentWithAux>, Error>
    where
        Self::Polynomial: 'a;

    fn batch_commit_and_write<'a>(
        pp: &Self::ProverParam,
        polys: impl IntoIterator<Item = &'a Self::Polynomial>,
        transcript: &mut impl TranscriptWrite<Self::Commitment, F>,
    ) -> Result<Vec<Self::CommitmentWithAux>, Error>
    where
        Self::Polynomial: 'a,
    {
        let comms = Self::batch_commit(pp, polys)?;
        for comm in comms.iter() {
            transcript.write_commitment(comm.as_ref())?;
        }
        Ok(comms)
    }

    fn open(
        pp: &Self::ProverParam,
        poly: &Self::Polynomial,
        comm: &Self::CommitmentWithAux,
        point: &Self::Point,
        eval: &F,
        transcript: &mut impl TranscriptWrite<Self::Commitment, F>,
    ) -> Result<(), Error>;

    fn batch_open<'a>(
        pp: &Self::ProverParam,
        polys: impl IntoIterator<Item = &'a Self::Polynomial>,
        comms: impl IntoIterator<Item = &'a Self::CommitmentWithAux>,
        points: &[Self::Point],
        evals: &[Evaluation<F>],
        transcript: &mut impl TranscriptWrite<Self::Commitment, F>,
    ) -> Result<(), Error>
    where
        Self::Polynomial: 'a,
        Self::CommitmentWithAux: 'a;

    fn verify(
        vp: &Self::VerifierParam,
        comm: &Self::Commitment,
        point: &Self::Point,
        eval: &F,
        transcript: &mut impl TranscriptRead<Self::Commitment, F>,
    ) -> Result<(), Error>;

    fn batch_verify(
        vp: &Self::VerifierParam,
        comms: &[Self::Commitment],
        points: &[Self::Point],
        evals: &[Evaluation<F>],
        transcript: &mut impl TranscriptRead<Self::Commitment, F>,
    ) -> Result<(), Error>;
}

#[derive(Clone, Debug)]
pub struct Evaluation<F: Field> {
    poly: usize,
    point: usize,
    value: F,
}

impl<F: Field> Evaluation<F> {
    pub fn new(poly: usize, point: usize, value: F) -> Self {
        Self { poly, point, value }
    }

    pub fn poly(&self) -> usize {
        self.poly
    }

    pub fn point(&self) -> usize {
        self.point
    }

    pub fn value(&self) -> &F {
        &self.value
    }
}