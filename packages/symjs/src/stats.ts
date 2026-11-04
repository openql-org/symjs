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

export { isRandom, FiniteDensity, RandomDomain, SingleDomain, ConditionalDomain, ProductDomain, PSpace, SinglePSpace, RandomSymbol, ProductPSpace, IndependentProductPSpace, Distribution, randomSymbols, pspace, given, expectation, P, Density, density, cdf, characteristicFunction, momentGeneratingFunction, where, quantile, dependent, independent } from './stats/rv';
export type { DensityResult, ComputeOptions, SingleSpace, ProbabilityOptions } from './stats/rv';
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
