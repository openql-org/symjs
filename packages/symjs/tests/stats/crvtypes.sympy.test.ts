// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/crvtypes.ts: the density, set and closed forms (SymPy
// _cdf, _characteristic_function, _moment_generating_function, _quantile)
// of every continuous distribution, generated from SymPy 1.14
// (str(dist.pdf(x)), str(dist._cdf(x)), ...). null: SymPy has no closed form.

import { describe, expect, it } from 'vitest';
import { Sym, mul, str } from '../../src';
import type { Expr } from '../../src';
import {
  Arcsin, Benini, Beta, BetaNoncentral, BetaPrime, BoundedPareto, Cauchy, ChiNoncentral, ChiRV, ChiSquared, Dagum, Davis, Erlang, ExGaussian,
  Exponential, ExponentialPower, FDistribution, FisherZ, Frechet, Gamma, GammaInverse, GaussianInverse, Gompertz, Gumbel, Kumaraswamy, Laplace,
  Levy, LogCauchy, LogLogistic, LogNormal, Logistic, LogitNormal, Lomax, Maxwell, Moyal, Nakagami, Normal, Pareto, PowerFunction, QuadraticU,
  RaisedCosine, Rayleigh, Reciprocal, ShiftedGompertz, SingleContinuousDistribution, StudentT, Trapezoidal, Triangular, Uniform, UniformSum, VonMises,
  Weibull, WignerSemicircle,
} from '../../src/stats';
import type { RandomSymbol } from '../../src/stats';

const [x, t, p] = ['x', 't', 'p'].map((n) => new Sym(n)) as [Sym, Sym, Sym];
const [a, b, c, k, l, mu, s, n] = ['a', 'b', 'c', 'k', 'l', 'mu', 's', 'n'].map((v) => new Sym(v, { positive: true })) as Sym[] as [Sym, Sym, Sym, Sym, Sym, Sym, Sym, Sym];
const r = new Sym('r', { real: true });
const ni = new Sym('n', { positive: true, integer: true });
const mi = new Sym('m', { positive: true, integer: true });
const pp = new Sym('p', { positive: true });

type Row = { dist: string; pdf: string; set: string; cdf: string | null; cf: string | null; mgf: string | null; quantile: string | null };
const TABLE: [string, () => RandomSymbol, Row][] = [
  ["Arcsin('X', a, b)", () => Arcsin('X', a, b), {"dist": "ArcsinDistribution(a, b)", "pdf": "1/(pi*sqrt((-a + x)*(b - x)))", "set": "Interval(a, b)", "cdf": "Piecewise((0, a > x), (2*asin(sqrt((-a + x)/(-a + b)))/pi, b >= x), (1, True))", "cf": null, "mgf": null, "quantile": null}],
  ["Arcsin('X')", () => Arcsin('X'), {"dist": "ArcsinDistribution(0, 1)", "pdf": "1/(pi*sqrt(x*(1 - x)))", "set": "Interval(0, 1)", "cdf": "Piecewise((0, x < 0), (2*asin(sqrt(x))/pi, x <= 1), (1, True))", "cf": null, "mgf": null, "quantile": null}],
  ["Benini('X', a, b, s)", () => Benini('X', a, b, s), {"dist": "BeniniDistribution(a, b, s)", "pdf": "(a/x + 2*b*log(x/s)/x)*exp(-a*log(x/s) - b*log(x/s)**2)", "set": "Interval(s, oo)", "cdf": null, "cf": null, "mgf": "NotImplementedError: The moment generating function of the Benini distribution does not exist.", "quantile": null}],
  ["Beta('X', a, b)", () => Beta('X', a, b), {"dist": "BetaDistribution(a, b)", "pdf": "x**(a - 1)*(1 - x)**(b - 1)/beta(a, b)", "set": "Interval(0, 1)", "cdf": null, "cf": "hyper((a,), (a + b,), I*t)", "mgf": "hyper((a,), (a + b,), t)", "quantile": null}],
  ["BetaNoncentral('X', a, b, l)", () => BetaNoncentral('X', a, b, l), {"dist": "BetaNoncentralDistribution(a, b, l)", "pdf": "Sum(x**(_k + a - 1)*(l/2)**_k*(1 - x)**(b - 1)*exp(-l/2)/(beta(_k + a, b)*factorial(_k)), (_k, 0, oo))", "set": "Interval(0, 1)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["BetaPrime('X', a, b)", () => BetaPrime('X', a, b), {"dist": "BetaPrimeDistribution(a, b)", "pdf": "x**(a - 1)*(x + 1)**(-a - b)/beta(a, b)", "set": "Interval(0, oo)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["BoundedPareto('X', a, 1, 2)", () => BoundedPareto('X', a, 1, 2), {"dist": "BoundedParetoDistribution(a, 1, 2)", "pdf": "a*x**(-a - 1)/(1 - (1/2)**a)", "set": "Interval(1, 2)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["Cauchy('X', r, s)", () => Cauchy('X', r, s), {"dist": "CauchyDistribution(r, s)", "pdf": "1/(pi*s*(1 + (-r + x)**2/s**2))", "set": "Interval(-oo, oo)", "cdf": "atan((-r + x)/s)/pi + 1/2", "cf": "exp(I*r*t - s*Abs(t))", "mgf": "NotImplementedError: The moment generating function for the Cauchy distribution does not exist.", "quantile": "r + s*tan(pi*(p - 1/2))"}],
  ["ChiRV('X', ni)", () => ChiRV('X', ni), {"dist": "ChiDistribution(n)", "pdf": "2**(1 - n/2)*x**(n - 1)*exp(-x**2/2)/gamma(n/2)", "set": "Interval(0, oo)", "cdf": null, "cf": "sqrt(2)*I*t*gamma(n/2 + 1/2)*hyper((n/2 + 1/2,), (3/2,), -t**2/2)/gamma(n/2) + hyper((n/2,), (1/2,), -t**2/2)", "mgf": "sqrt(2)*t*gamma(n/2 + 1/2)*hyper((n/2 + 1/2,), (3/2,), t**2/2)/gamma(n/2) + hyper((n/2,), (1/2,), t**2/2)", "quantile": null}],
  ["ChiNoncentral('X', ni, l)", () => ChiNoncentral('X', ni, l), {"dist": "ChiNoncentralDistribution(n, l)", "pdf": "l*x**n*exp(-l**2/2 - x**2/2)*besseli(n/2 - 1, l*x)/(l*x)**(n/2)", "set": "Interval(0, oo)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["ChiSquared('X', ni)", () => ChiSquared('X', ni), {"dist": "ChiSquaredDistribution(n)", "pdf": "x**(n/2 - 1)*exp(-x/2)/(2**(n/2)*gamma(n/2))", "set": "Interval(0, oo)", "cdf": "Piecewise((lowergamma(n/2, x/2)/gamma(n/2), x >= 0), (0, True))", "cf": "(-2*I*t + 1)**(-n/2)", "mgf": "(1 - 2*t)**(-n/2)", "quantile": null}],
  ["Dagum('X', pp, a, b)", () => Dagum('X', pp, a, b), {"dist": "DagumDistribution(p, a, b)", "pdf": "a*p*(x/b)**(a*p)*((x/b)**a + 1)**(-p - 1)/x", "set": "Interval(0, oo)", "cdf": "Piecewise(((1 + (x/b)**(-a))**(-p), x >= 0), (0, True))", "cf": null, "mgf": null, "quantile": null}],
  ["Davis('X', b, 2, mu)", () => Davis('X', b, 2, mu), {"dist": "DavisDistribution(b, 2, mu)", "pdf": "6*b**2/(pi**2*(-mu + x)**3*(exp(b/(-mu + x)) - 1))", "set": "Interval(0, oo)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["Erlang('X', k, l)", () => Erlang('X', k, l), {"dist": "GammaDistribution(k, 1/l)", "pdf": "l**k*x**(k - 1)*exp(-l*x)/gamma(k)", "set": "Interval(0, oo)", "cdf": "Piecewise((lowergamma(k, l*x)/gamma(k), x > 0), (0, True))", "cf": "(1 - I*t/l)**(-k)", "mgf": "(1 - t/l)**(-k)", "quantile": null}],
  ["ExGaussian('X', r, s, l)", () => ExGaussian('X', r, s, l), {"dist": "ExGaussianDistribution(r, s, l)", "pdf": "l*exp(l*(l*s**2 + 2*r - 2*x)/2)*erfc(sqrt(2)*(l*s**2 + r - x)/(2*s))/2", "set": "Interval(-oo, oo)", "cdf": "-(erf(sqrt(2)*(-l**2*s**2 + l*(-r + x))/(2*l*s))/2 + 1/2)*exp(l**2*s**2/2 - l*(-r + x)) + erf(sqrt(2)*(-r + x)/(2*s))/2 + 1/2", "cf": "exp(I*r*t - s**2*t**2/2)/(1 - I*t/l)", "mgf": "exp(r*t + s**2*t**2/2)/(1 - t/l)", "quantile": null}],
  ["Exponential('X', l)", () => Exponential('X', l), {"dist": "ExponentialDistribution(l)", "pdf": "l*exp(-l*x)", "set": "Interval(0, oo)", "cdf": "Piecewise((1 - exp(-l*x), x >= 0), (0, True))", "cf": "l/(l - I*t)", "mgf": "l/(l - t)", "quantile": "-log(1 - p)/l"}],
  ["ExponentialPower('X', r, a, b)", () => ExponentialPower('X', r, a, b), {"dist": "ExponentialPowerDistribution(r, a, b)", "pdf": "b*exp(-(Abs(r - x)/a)**b)/(2*a*gamma(1/b))", "set": "Interval(-oo, oo)", "cdf": "1/2 + lowergamma(1/b, (Abs(r - x)/a)**b)*sign(-r + x)/(2*gamma(1/b))", "cf": null, "mgf": null, "quantile": null}],
  ["FDistribution('X', ni, mi)", () => FDistribution('X', ni, mi), {"dist": "FDistributionDistribution(n, m)", "pdf": "m**(m/2)*sqrt((n*x)**n*(m + n*x)**(-m - n))/(x*beta(n/2, m/2))", "set": "Interval(0, oo)", "cdf": null, "cf": null, "mgf": "NotImplementedError: The moment generating function for the F-distribution does not exist.", "quantile": null}],
  ["FisherZ('X', a, b)", () => FisherZ('X', a, b), {"dist": "FisherZDistribution(a, b)", "pdf": "2*a**(a/2)*b**(b/2)*(a*exp(2*x) + b)**(-a/2 - b/2)*exp(a*x)/beta(a/2, b/2)", "set": "Interval(-oo, oo)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["Frechet('X', a, s, mu)", () => Frechet('X', a, s, mu), {"dist": "FrechetDistribution(a, s, mu)", "pdf": "a*((-mu + x)/s)**(-a - 1)*exp(-1/((-mu + x)/s)**a)/s", "set": "Interval(0, oo)", "cdf": "Piecewise((exp(-1/((-mu + x)/s)**a), mu <= x), (0, True))", "cf": null, "mgf": null, "quantile": null}],
  ["Frechet('X', a)", () => Frechet('X', a), {"dist": "FrechetDistribution(a, 1, 0)", "pdf": "a*x**(-a - 1)*exp(-1/x**a)", "set": "Interval(0, oo)", "cdf": "Piecewise((exp(-1/x**a), x >= 0), (0, True))", "cf": null, "mgf": null, "quantile": null}],
  ["Gamma('X', k, s)", () => Gamma('X', k, s), {"dist": "GammaDistribution(k, s)", "pdf": "x**(k - 1)*exp(-x/s)/(s**k*gamma(k))", "set": "Interval(0, oo)", "cdf": "Piecewise((lowergamma(k, x/s)/gamma(k), x > 0), (0, True))", "cf": "(-I*s*t + 1)**(-k)", "mgf": "(-s*t + 1)**(-k)", "quantile": null}],
  ["GammaInverse('X', a, b)", () => GammaInverse('X', a, b), {"dist": "GammaInverseDistribution(a, b)", "pdf": "b**a*x**(-a - 1)*exp(-b/x)/gamma(a)", "set": "Interval(0, oo)", "cdf": "Piecewise((uppergamma(a, b/x)/gamma(a), x > 0), (0, True))", "cf": "2*(-I*b*t)**(a/2)*besselk(a, 2*sqrt(b)*sqrt(-I*t))/gamma(a)", "mgf": "NotImplementedError: The moment generating function for the gamma inverse distribution does not exist.", "quantile": null}],
  ["Gumbel('X', b, r)", () => Gumbel('X', b, r), {"dist": "GumbelDistribution(b, r, False)", "pdf": "exp(-exp(-(-r + x)/b) - (-r + x)/b)/b", "set": "Interval(-oo, oo)", "cdf": "exp(-exp(-(-r + x)/b))", "cf": "exp(I*r*t)*gamma(-I*b*t + 1)", "mgf": "exp(r*t)*gamma(-b*t + 1)", "quantile": null}],
  ["Gumbel('X', b, r, true)", () => Gumbel('X', b, r, true), {"dist": "GumbelDistribution(b, r, True)", "pdf": "exp(-exp((-r + x)/b) + (-r + x)/b)/b", "set": "Interval(-oo, oo)", "cdf": "1 - exp(-exp((-r + x)/b))", "cf": "exp(I*r*t)*gamma(I*b*t + 1)", "mgf": "exp(r*t)*gamma(b*t + 1)", "quantile": null}],
  ["Gompertz('X', b, a)", () => Gompertz('X', b, a), {"dist": "GompertzDistribution(b, a)", "pdf": "a*b*exp(a)*exp(-a*exp(b*x))*exp(b*x)", "set": "Interval(0, oo)", "cdf": "-exp(a)*exp(-a*exp(b*x)) + 1", "cf": null, "mgf": "a*exp(a)*expint(t/b, a)", "quantile": null}],
  ["Kumaraswamy('X', a, b)", () => Kumaraswamy('X', a, b), {"dist": "KumaraswamyDistribution(a, b)", "pdf": "a*b*x**(a - 1)*(1 - x**a)**(b - 1)", "set": "Interval(0, oo)", "cdf": "Piecewise((0, x < 0), (1 - (1 - x**a)**b, x <= 1), (1, True))", "cf": null, "mgf": null, "quantile": null}],
  ["Laplace('X', r, b)", () => Laplace('X', r, b), {"dist": "LaplaceDistribution(r, b)", "pdf": "exp(-Abs(r - x)/b)/(2*b)", "set": "Interval(-oo, oo)", "cdf": "Piecewise((exp((-r + x)/b)/2, r > x), (1 - exp((r - x)/b)/2, True))", "cf": "exp(I*r*t)/(b**2*t**2 + 1)", "mgf": "exp(r*t)/(-b**2*t**2 + 1)", "quantile": null}],
  ["Levy('X', r, c)", () => Levy('X', r, c), {"dist": "LevyDistribution(r, c)", "pdf": "sqrt(2)*sqrt(c)*exp(-c/(-2*r + 2*x))/(2*sqrt(pi)*(-r + x)**(3/2))", "set": "Interval(r, oo)", "cdf": "erfc(sqrt(c)*sqrt(1/(-2*r + 2*x)))", "cf": "exp(-sqrt(2)*sqrt(c)*sqrt(-I*t) + I*r*t)", "mgf": "NotImplementedError: The moment generating function of Levy distribution does not exist.", "quantile": null}],
  ["LogCauchy('X', r, s)", () => LogCauchy('X', r, s), {"dist": "LogCauchyDistribution(r, s)", "pdf": "s/(pi*x*(s**2 + (-r + log(x))**2))", "set": "Interval.open(0, oo)", "cdf": "atan((-r + log(x))/s)/pi + 1/2", "cf": "NotImplementedError: The characteristic function for the Log-Cauchy distribution does not exist.", "mgf": "NotImplementedError: The moment generating function for the Log-Cauchy distribution does not exist.", "quantile": null}],
  ["Logistic('X', r, s)", () => Logistic('X', r, s), {"dist": "LogisticDistribution(r, s)", "pdf": "exp((r - x)/s)/(s*(exp((r - x)/s) + 1)**2)", "set": "Interval(-oo, oo)", "cdf": "1/(exp((r - x)/s) + 1)", "cf": "Piecewise((pi*s*t*exp(I*r*t)/sinh(pi*s*t), Ne(t, 0)), (1, True))", "mgf": "exp(r*t)*beta(-s*t + 1, s*t + 1)", "quantile": "r - s*log(-1 + 1/p)"}],
  ["LogLogistic('X', a, b)", () => LogLogistic('X', a, b), {"dist": "LogLogisticDistribution(a, b)", "pdf": "b*(x/a)**(b - 1)/(a*((x/a)**b + 1)**2)", "set": "Interval(0, oo)", "cdf": "1/(1 + (x/a)**(-b))", "cf": null, "mgf": null, "quantile": "a*(p/(1 - p))**(1/b)"}],
  ["LogitNormal('X', r, s)", () => LogitNormal('X', r, s), {"dist": "LogitNormalDistribution(r, s)", "pdf": "sqrt(2)*exp(-(-r + log(x/(1 - x)))**2/(2*s**2))/(2*sqrt(pi)*s*x*(1 - x))", "set": "Interval.open(0, 1)", "cdf": "erf(sqrt(2)*(-r + log(x/(1 - x)))/(2*s))/2 + 1/2", "cf": null, "mgf": null, "quantile": null}],
  ["LogNormal('X', r, s)", () => LogNormal('X', r, s), {"dist": "LogNormalDistribution(r, s)", "pdf": "sqrt(2)*exp(-(-r + log(x))**2/(2*s**2))/(2*sqrt(pi)*s*x)", "set": "Interval(0, oo)", "cdf": "Piecewise((erf(sqrt(2)*(-r + log(x))/(2*s))/2 + 1/2, x > 0), (0, True))", "cf": null, "mgf": "NotImplementedError: Moment generating function of the log-normal distribution is not defined.", "quantile": null}],
  ["Lomax('X', a, l)", () => Lomax('X', a, l), {"dist": "LomaxDistribution(a, l)", "pdf": "a*(1 + x/l)**(-a - 1)/l", "set": "Interval(0, oo)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["Maxwell('X', a)", () => Maxwell('X', a), {"dist": "MaxwellDistribution(a)", "pdf": "sqrt(2)*x**2*exp(-x**2/(2*a**2))/(sqrt(pi)*a**3)", "set": "Interval(0, oo)", "cdf": "erf(sqrt(2)*x/(2*a)) - sqrt(2)*x*exp(-x**2/(2*a**2))/(sqrt(pi)*a)", "cf": null, "mgf": null, "quantile": null}],
  ["Moyal('X', r, s)", () => Moyal('X', r, s), {"dist": "MoyalDistribution(r, s)", "pdf": "sqrt(2)*exp(-exp((r - x)/s)/2 - (-r + x)/(2*s))/(2*sqrt(pi)*s)", "set": "Interval(-oo, oo)", "cdf": null, "cf": "exp(I*r*t)*gamma(-I*s*t + 1/2)/(2**(I*s*t)*sqrt(pi))", "mgf": "exp(r*t)*gamma(-s*t + 1/2)/(2**(s*t)*sqrt(pi))", "quantile": null}],
  ["Nakagami('X', mu, s)", () => Nakagami('X', mu, s), {"dist": "NakagamiDistribution(mu, s)", "pdf": "2*mu**mu*x**(2*mu - 1)*exp(-mu*x**2/s)/(s**mu*gamma(mu))", "set": "Interval(0, oo)", "cdf": "Piecewise((lowergamma(mu, mu*x**2/s)/gamma(mu), x > 0), (0, True))", "cf": null, "mgf": null, "quantile": null}],
  ["Normal('X', r, s)", () => Normal('X', r, s), {"dist": "NormalDistribution(r, s)", "pdf": "sqrt(2)*exp(-(-r + x)**2/(2*s**2))/(2*sqrt(pi)*s)", "set": "Interval(-oo, oo)", "cdf": "erf(sqrt(2)*(-r + x)/(2*s))/2 + 1/2", "cf": "exp(I*r*t - s**2*t**2/2)", "mgf": "exp(r*t + s**2*t**2/2)", "quantile": "r + sqrt(2)*s*erfinv(2*p - 1)"}],
  ["GaussianInverse('X', mu, l)", () => GaussianInverse('X', mu, l), {"dist": "GaussianInverseDistribution(mu, l)", "pdf": "sqrt(2)*sqrt(l)*sqrt(x**(-3))*exp(-l*(-mu + x)**2/(2*mu**2*x))/(2*sqrt(pi))", "set": "Interval(0, oo)", "cdf": "(1/2 - erf(sqrt(2)*sqrt(l)*(1 + x/mu)*sqrt(1/x)/2)/2)*exp(2*l/mu) + erf(sqrt(2)*sqrt(l)*(-1 + x/mu)*sqrt(1/x)/2)/2 + 1/2", "cf": "exp(l*(1 - sqrt(1 - 2*I*mu**2*t/l))/mu)", "mgf": "exp(l*(1 - sqrt(1 - 2*mu**2*t/l))/mu)", "quantile": null}],
  ["Pareto('X', a, b)", () => Pareto('X', a, b), {"dist": "ParetoDistribution(a, b)", "pdf": "a**b*b*x**(-b - 1)", "set": "Interval(a, oo)", "cdf": "Piecewise((-a**b/x**b + 1, a <= x), (0, True))", "cf": "b*(-I*a*t)**b*uppergamma(-b, -I*a*t)", "mgf": "b*(-a*t)**b*uppergamma(-b, -a*t)", "quantile": null}],
  ["PowerFunction('X', a, 0, 1)", () => PowerFunction('X', a, 0, 1), {"dist": "PowerFunctionDistribution(a, 0, 1)", "pdf": "a*x**(a - 1)", "set": "Interval(0, 1)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["QuadraticU('X', 1, 3)", () => QuadraticU('X', 1, 3), {"dist": "QuadraticUDistribution(1, 3)", "pdf": "Piecewise((3*(x - 2)**2/2, (x >= 1) & (x <= 3)), (0, True))", "set": "Interval(1, 3)", "cdf": null, "cf": "3*I*(-4*t + 4*I)*exp(I*t*exp(3*I*t))/(8*t**2)", "mgf": "-(3*(4*t + 4)*exp(3*t) - 3*(12*t + 4)*exp(t))/(8*t**2)", "quantile": null}],
  ["RaisedCosine('X', r, s)", () => RaisedCosine('X', r, s), {"dist": "RaisedCosineDistribution(r, s)", "pdf": "Piecewise(((cos(pi*(-r + x)/s) + 1)/(2*s), (x <= r + s) & (x >= r - s)), (0, True))", "set": "Interval(r - s, r + s)", "cdf": null, "cf": "Piecewise((exp(-I*pi*r/s)/2, Eq(t, -pi/s)), (exp(I*pi*r/s)/2, Eq(t, pi/s)), (pi**2*exp(I*r*t)*sin(s*t)/(s*t*(-s**2*t**2 + pi**2)), True))", "mgf": "pi**2*exp(r*t)*sinh(s*t)/(s*t*(s**2*t**2 + pi**2))", "quantile": null}],
  ["Rayleigh('X', s)", () => Rayleigh('X', s), {"dist": "RayleighDistribution(s)", "pdf": "x*exp(-x**2/(2*s**2))/s**2", "set": "Interval(0, oo)", "cdf": "1 - exp(-x**2/(2*s**2))", "cf": "-sqrt(2)*sqrt(pi)*s*t*(erfi(sqrt(2)*s*t/2) - I)*exp(-s**2*t**2/2)/2 + 1", "mgf": "sqrt(2)*sqrt(pi)*s*t*(erf(sqrt(2)*s*t/2) + 1)*exp(s**2*t**2/2)/2 + 1", "quantile": null}],
  ["Reciprocal('X', a, 2*a)", () => Reciprocal('X', a, mul(2, a)), {"dist": "ReciprocalDistribution(a, 2*a)", "pdf": "1/(x*(-log(a) + log(2*a)))", "set": "Interval(a, 2*a)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["ShiftedGompertz('X', b, a)", () => ShiftedGompertz('X', b, a), {"dist": "ShiftedGompertzDistribution(b, a)", "pdf": "b*(a*(1 - exp(-b*x)) + 1)*exp(-a*exp(-b*x))*exp(-b*x)", "set": "Interval(0, oo)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["StudentT('X', n)", () => StudentT('X', n), {"dist": "StudentTDistribution(n)", "pdf": "(1 + x**2/n)**(-n/2 - 1/2)/(sqrt(n)*beta(1/2, n/2))", "set": "Interval(-oo, oo)", "cdf": "1/2 + x*gamma(n/2 + 1/2)*hyper((1/2, n/2 + 1/2), (3/2,), -x**2/n)/(sqrt(pi)*sqrt(n)*gamma(n/2))", "cf": null, "mgf": "NotImplementedError: The moment generating function for the Student-T distribution is undefined.", "quantile": null}],
  ["Trapezoidal('X', 1, 2, 3, 4)", () => Trapezoidal('X', 1, 2, 3, 4), {"dist": "TrapezoidalDistribution(1, 2, 3, 4)", "pdf": "Piecewise((x/2 - 1/2, (x >= 1) & (x < 2)), (1/2, (x >= 2) & (x < 3)), (2 - x/2, (x >= 3) & (x <= 4)), (0, True))", "set": "Interval(1, 4)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["Triangular('X', 1, 3, 2)", () => Triangular('X', 1, 3, 2), {"dist": "TriangularDistribution(1, 3, 2)", "pdf": "Piecewise((x - 1, (x >= 1) & (x < 2)), (1, Eq(x, 2)), (3 - x, (x <= 3) & (x > 2)), (0, True))", "set": "Interval(1, 3)", "cdf": null, "cf": "(-2*exp(3*I*t) + 4*exp(2*I*t) - 2*exp(I*t))/(2*t**2)", "mgf": "(2*exp(3*t) - 4*exp(2*t) + 2*exp(t))/(2*t**2)", "quantile": null}],
  ["Uniform('X', 0, a)", () => Uniform('X', 0, a), {"dist": "UniformDistribution(0, a)", "pdf": "Piecewise((1/a, (a >= x) & (x >= 0)), (0, True))", "set": "Interval(0, a)", "cdf": "Piecewise((0, x < 0), (x/a, a >= x), (1, True))", "cf": "Piecewise((-I*(exp(I*a*t) - 1)/(a*t), Ne(t, 0)), (1, True))", "mgf": "Piecewise(((exp(a*t) - 1)/(a*t), Ne(t, 0)), (1, True))", "quantile": null}],
  ["UniformSum('X', ni)", () => UniformSum('X', ni), {"dist": "UniformSumDistribution(n)", "pdf": "Sum((-1)**_k*(-_k + x)**(n - 1)*binomial(n, _k), (_k, 0, floor(x)))/factorial(n - 1)", "set": "Interval(0, n)", "cdf": "Piecewise((0, x < 0), (Sum((-1)**_k*(-_k + x)**n*binomial(n, _k), (_k, 0, floor(x)))/factorial(n), n >= x), (1, True))", "cf": "(-I*(exp(I*t) - 1)/t)**n", "mgf": "((exp(t) - 1)/t)**n", "quantile": null}],
  ["VonMises('X', r, k)", () => VonMises('X', r, k), {"dist": "VonMisesDistribution(r, k)", "pdf": "exp(k*cos(r - x))/(2*pi*besseli(0, k))", "set": "Interval(0, 2*pi)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["Weibull('X', a, b)", () => Weibull('X', a, b), {"dist": "WeibullDistribution(a, b)", "pdf": "b*(x/a)**(b - 1)*exp(-(x/a)**b)/a", "set": "Interval(0, oo)", "cdf": null, "cf": null, "mgf": null, "quantile": null}],
  ["WignerSemicircle('X', a)", () => WignerSemicircle('X', a), {"dist": "WignerSemicircleDistribution(a)", "pdf": "2*sqrt(a**2 - x**2)/(pi*a**2)", "set": "Interval(-a, a)", "cdf": null, "cf": "Piecewise((2*besselj(1, a*t)/(a*t), Ne(t, 0)), (1, True))", "mgf": "Piecewise((2*besseli(1, a*t)/(a*t), Ne(t, 0)), (1, True))", "quantile": null}],
];

const distOf = (X: RandomSymbol): SingleContinuousDistribution => (X.pspace as unknown as { distribution: SingleContinuousDistribution }).distribution;

/** The closed form (or the NotImplementedError message) of SymPy, compared with the public method that uses it. */
function closed(expected: string | null, f: () => Expr): void {
  if (expected === null) return;
  if (expected.startsWith('NotImplementedError: ')) {
    expect(f).toThrow(expected.slice('NotImplementedError: '.length));
    return;
  }
  expect(str(f())).toBe(expected);
}

// QuadraticU: SymPy's closed forms are wrong (the mean they give for QuadraticU(1, 3) is -11, not 2); see crvtypes.test.ts
const SYMPY_WRONG = new Set(["QuadraticU('X', 1, 3)"]);

// chunks of the table, so that each test stays short
for (let i = 0; i < TABLE.length; i += 10) {
  describe(`continuous distributions ${i + 1}-${Math.min(i + 10, TABLE.length)}`, () => {
    for (const [src, make, row] of TABLE.slice(i, i + 10)) {
      it(src, () => {
        const d = distOf(make());
        expect(str(d)).toBe(row.dist);
        expect(str(d.pdf(x))).toBe(row.pdf);
        expect(str(d.set)).toBe(row.set);
        closed(row.cdf, () => d.cdf(x));
        closed(row.quantile, () => d.quantile(p));
        if (SYMPY_WRONG.has(src)) return;
        closed(row.cf, () => d.characteristicFunction(t));
        closed(row.mgf, () => d.momentGeneratingFunction(t));
      });
    }
  });
}
// the symbols are all used by the table
void [a, b, c, k, l, mu, s, n, r, ni, mi, pp];
