// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/stats`: probability and statistics with
 * random symbols (SymPy sympy.stats): continuous, discrete and finite
 * distributions, compound distributions, the probability functions
 * (`P`, `expectation`, `density`, `given`, `where`, `cdf`, ...), moments
 * and other statistics, and the unevaluated Probability, Expectation,
 * Variance, Covariance, Moment and CentralMoment nodes.
 *
 * SymPy's `E` (the expectation) is exported as `expectation`, SymPy's own
 * name for it (`E` is Euler's number), and the Chi distribution as `ChiRV`
 * (`Chi` is the hyperbolic cosine integral); see docs/api-policy.md.
 */

// every entry point brings the core with its registrations
import './core';

export { isRandom, FiniteDensity, RandomDomain, SingleDomain, MatrixDomain, ConditionalDomain, ProductDomain, PSpace, SinglePSpace, RandomSymbol, ProductPSpace, IndependentProductPSpace, RandomIndexedSymbol, RandomMatrixSymbol, Distribution, randomSymbols, pspace, given, expectation, P, Density, density, cdf, characteristicFunction, momentGeneratingFunction, where, quantile, dependent, independent } from './stats/rv';
export type { DensityResult, ComputeOptions, SingleSpace, ProbabilityOptions, MatrixParam } from './stats/rv';
export { moment, variance, std, entropy, H, covariance, correlation, cmoment, smoment, skewness, kurtosis, factorialMoment, median, coskewness } from './stats/rvinterface';
export type { EntropyOptions } from './stats/rvinterface';
export { SingleContinuousDomain, ProductContinuousDomain, ConditionalContinuousDomain, ContinuousDistribution, SingleContinuousDistribution, ContinuousPSpace, SingleContinuousPSpace } from './stats/crv';
export type { ClosedForm } from './stats/crv';
export { ContinuousDistributionHandmade, ContinuousRV, ArcsinDistribution, Arcsin, BeniniDistribution, Benini, BetaDistribution, Beta, BetaNoncentralDistribution, BetaNoncentral, BetaPrimeDistribution, BetaPrime, BoundedParetoDistribution, BoundedPareto, CauchyDistribution, Cauchy, ChiDistribution, ChiRV, ChiNoncentralDistribution, ChiNoncentral, ChiSquaredDistribution, ChiSquared, DagumDistribution, Dagum, DavisDistribution, Davis, Erlang, ExGaussianDistribution, ExGaussian, ExponentialDistribution, Exponential, ExponentialPowerDistribution, ExponentialPower, FDistributionDistribution, FDistribution, FisherZDistribution, FisherZ, FrechetDistribution, Frechet, GammaDistribution, Gamma, GammaInverseDistribution, GammaInverse, GumbelDistribution, Gumbel, GompertzDistribution, Gompertz, KumaraswamyDistribution, Kumaraswamy, LaplaceDistribution, Laplace, LevyDistribution, Levy, LogCauchyDistribution, LogCauchy, LogisticDistribution, Logistic, LogLogisticDistribution, LogLogistic, LogitNormalDistribution, LogitNormal, LogNormalDistribution, LogNormal, LomaxDistribution, Lomax, MaxwellDistribution, Maxwell, MoyalDistribution, Moyal, NakagamiDistribution, Nakagami, NormalDistribution, Normal, GaussianInverseDistribution, GaussianInverse, Wald, ParetoDistribution, Pareto, PowerFunctionDistribution, PowerFunction, QuadraticUDistribution, QuadraticU, RaisedCosineDistribution, RaisedCosine, RayleighDistribution, Rayleigh, ReciprocalDistribution, Reciprocal, ShiftedGompertzDistribution, ShiftedGompertz, StudentTDistribution, StudentT, TrapezoidalDistribution, Trapezoidal, TriangularDistribution, Triangular, UniformDistribution, Uniform, UniformSumDistribution, UniformSum, VonMisesDistribution, VonMises, WeibullDistribution, Weibull, WignerSemicircleDistribution, WignerSemicircle } from './stats/crvtypes';
export type { RVOptions } from './stats/crvtypes';
export { DiscreteDistribution, SingleDiscreteDistribution, DiscreteDomain, SingleDiscreteDomain, ConditionalDiscreteDomain, DiscretePSpace, ProductDiscreteDomain, SingleDiscretePSpace } from './stats/drv';
export { DiscreteDistributionHandmade, DiscreteRV, FlorySchulzDistribution, FlorySchulz, GeometricDistribution, Geometric, HermiteDistribution, Hermite, LogarithmicDistribution, Logarithmic, NegativeBinomialDistribution, NegativeBinomial, PoissonDistribution, Poisson, SkellamDistribution, Skellam, YuleSimonDistribution, YuleSimon, ZetaDistribution, Zeta } from './stats/drvtypes';
export { FiniteDomain, SingleFiniteDomain, ProductFiniteDomain, ConditionalFiniteDomain, SingleFiniteDistribution, FinitePSpace, SingleFinitePSpace, ProductFinitePSpace } from './stats/frv';
export { FiniteDistributionHandmade, FiniteRV, DiscreteUniformDistribution, DiscreteUniform, DieDistribution, Die, BernoulliDistribution, Bernoulli, Coin, BinomialDistribution, Binomial, BetaBinomialDistribution, BetaBinomial, HypergeometricDistribution, Hypergeometric, RademacherDistribution, Rademacher, IdealSolitonDistribution, IdealSoliton, RobustSolitonDistribution, RobustSoliton } from './stats/frvtypes';
export { CompoundDistribution, CompoundPSpace } from './stats/compoundrv';
export { ProbabilityNode, Probability, ExpectationNode, Expectation, VarianceNode, Variance, CovarianceNode, Covariance, MomentNode, Moment, CentralMomentNode, CentralMoment } from './stats/symbolicprobability';
export type { ProbabilityDoitHints } from './stats/symbolicprobability';
export { varianceProp } from './stats/errorprop';
export type { VariancePropOptions } from './stats/errorprop';
export { JointDistribution, JointPSpace, JointRandomSymbol, MarginalDistribution } from './stats/jointrv';
export { marginalDistribution, JointDistributionHandmade, JointRV, MultivariateNormalDistribution, MultivariateNormal, MultivariateLaplaceDistribution, MultivariateLaplace, MultivariateTDistribution, MultivariateT, NormalGammaDistribution, NormalGamma, MultivariateBetaDistribution, MultivariateBeta, Dirichlet, MultivariateEwensDistribution, MultivariateEwens, GeneralizedMultivariateLogGammaDistribution, GeneralizedMultivariateLogGamma, GeneralizedMultivariateLogGammaOmega, MultinomialDistribution, Multinomial, NegativeMultinomialDistribution, NegativeMultinomial } from './stats/jointrvtypes';
export { ExpectationMatrixNode, ExpectationMatrix, VarianceMatrixNode, VarianceMatrix, CrossCovarianceMatrixNode, CrossCovarianceMatrix } from './stats/symbolicmultivariateprobability';
export { MatrixPSpace, MatrixDistribution, MatrixGammaDistribution, MatrixGamma, WishartDistribution, Wishart, MatrixNormalDistribution, MatrixNormal, MatrixStudentTDistribution, MatrixStudentT } from './stats/matrixdistributions';
export type { MatrixInput } from './stats/matrixdistributions';
export { RandomMatrixPSpace } from './stats/randommatrix';
export type { RandomMatrixModel } from './stats/randommatrix';
export { RandomMatrixEnsembleModel, GaussianEnsembleModel, GaussianUnitaryEnsembleModel, GaussianOrthogonalEnsembleModel, GaussianSymplecticEnsembleModel, CircularEnsembleModel, CircularUnitaryEnsembleModel, CircularOrthogonalEnsembleModel, CircularSymplecticEnsembleModel, GaussianEnsemble, GaussianUnitaryEnsemble, GaussianOrthogonalEnsemble, GaussianSymplecticEnsemble, CircularEnsemble, CircularUnitaryEnsemble, CircularOrthogonalEnsemble, CircularSymplecticEnsemble, jointEigenDistribution, JointEigenDistribution, levelSpacingDistribution } from './stats/randommatrixmodels';
export { StochasticPSpace, UnspecifiedDistribution } from './stats/stochasticprocess';
export type { ProcessLike } from './stats/stochasticprocess';
export { StochasticProcess, DiscreteTimeStochasticProcess, ContinuousTimeStochasticProcess, TransitionMatrixOfNode, TransitionMatrixOf, GeneratorMatrixOfNode, GeneratorMatrixOf, StochasticStateSpaceOfNode, StochasticStateSpaceOf, MarkovProcess, DiscreteMarkovChainNode, DiscreteMarkovChain, ContinuousMarkovChainNode, ContinuousMarkovChain, BernoulliProcessNode, BernoulliProcess, CountingProcess, PoissonProcessNode, PoissonProcess, WienerProcessNode, WienerProcess, GammaProcessNode, GammaProcess } from './stats/stochasticprocesstypes';
export type { StateSpaceInput, TransitionMatrixInput } from './stats/stochasticprocesstypes';
