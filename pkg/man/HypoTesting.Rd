\name{HypoTesting}
\alias{HypoTesting}

\title{Wald-Type Hypothesis Testing}
\description{Wald-type hypothesis tes for testing equality of high or extreme expectiles and quantiles}
\usage{
HypoTesting(data, tau, tau1=NULL, type="ExpectRisks", level="extreme",
            method="LAWS", bias=FALSE, k=NULL, alpha=0.05)
}
\arguments{
	\item{data}{A matrix of \eqn{(n \times d)}{(n x d)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}.}
	\item{tau1}{A real in \eqn{(0,1)} specifying the extreme level \eqn{\tau'_n}. See \bold{Details}.}
    \item{type}{A string specifying the type of test. By default \code{type="ExpectRisks"} specifies the test for testing the equality of expectiles. See \bold{Details}.}
    \item{level}{A string specifying the level of the expectile. This make sense when \code{type="ExpectRisks"}. By default \code{level="extreme"} specifies that the test concerns expectiles at the extreme level. See \bold{Details}.}
	\item{method}{A string specifying the method used to estimate the expecile. By default \code{est="LAWS"} specifies the use of the LAWS based estimator. See \bold{Details}.}
	\item{bias}{A logical value. By default \code{bias=FALSE} specifies that no bias correction is computed. See \bold{Details}.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the significance level of the test.}
}

\details{
	 With a dataset \code{data} of \code{d}-dimensional observations and sample size \eqn{n}, a Wald-type hypothesis testing is performed in order to check whether the is empirical evidence against the null hypothesis. The null hypothesis concerns the equality among the expectiles or quantiles or tail indices of the marginal distributions. The three tests depend on the depends on the estimation of the \code{d}-dimensional tail index \eqn{\gamma}. Here, \eqn{\gamma} is estimated using the Hill estimation (see \link{MultiHTailIndex} for details).
	 The data are regarded as \code{d}-dimensional temporal independent observations coming from dependent variables. See Padoan and Stupfler (2020) for details.
	\itemize{
		\item The so-called intermediate level \code{tau} or \eqn{\tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. Practically, for each marginal distribution, \eqn{\tau_n \in (0,1)}{\tau_n in (0,1)} is the ratio between \emph{N} (Numerator) and \emph{D} (Denominator). Where \emph{N} is the empirical mean distance of the \eqn{\tau_n}-\emph{th} expectile from the observations smaller than it, and \emph{D} is the empirical mean distance of \eqn{\tau_n}-\emph{th} expectile from all the observations.
		\item The so-called extreme level \code{tau1} or \eqn{\tau'_n} is a sequence of positive reals such that \eqn{\tau'_n \to 1}{\tau'_n -> 1} as \eqn{n \to \infty}{n -> \infty}.
		For each marginal distribution, the value \eqn{(1-tau'_n) \in (0,1)}{(1-tau'_n) in (0,1)} is meant to be a small tail probability such that \eqn{(1-\tau'_n)=1/n} or \eqn{(1-\tau'_n) < 1/n}. It is also assumed that \eqn{n(1-\tau'_n) \to C}{n(1-\tau'_n) -> C} as \eqn{n \to \infty}{n -> \infty}, where \eqn{C} is a positive finite constant. Typically, \eqn{C \in (0,1)}{C in (0,1)} so it is expected that there are no observations in a data sample that are greater than the expectile at the extreme level \eqn{\tau_n'}.
        \item When \code{type="ExpectRisks"}, the null hypothesis of the hypothesis testing concerns the equality among the expectiles of the marginal distributions. See Section 3.3 of Padoan and Stupfler (2020) for details. When \code{type="QuantRisks"}, the null hypothesis of the hypothesis testing concerns the equality among the quantiles of the marginal distributions. See Section 5 of Padoan and Stupfler (2020) for details. Note that in this case the test is based on the asymptotic distribution of normalized quantile estimator in the logarithmic scale. When \code{type="tails"}, the null hypothesis of the hypothesis testing concerns the equality among the tail indices of the marginal distributions. See Sections 3.2 and 3.3 of Padoan and Stupfler (2020) for details.
        \item When \code{type="ExpectRisks"}, the null hypothesis concerns the equality among the expectiles of the marginal distributions at the intermediate level and this is achieved through \code{level=="inter"}. In this case the test is obtained exploiting the asymptotic distribution of relative expectile appropriately normalised. See Section 2.1, 3.1 and 3.3 of Padoan and Stupfler (2020) for details. Instead, if \code{level=="extreme"} the null hypothesis concerns the equality among the expectiles of the marginal distributions at the extreme level.
		\item When \code{method='LAWS'}, then the \eqn{\tau'_n}-\emph{th} \code{d}-dimensional expectile is estimated using the LAWS based estimator. When \code{method='QB'}, the expectile is instead estimated using the QB esimtator. The definition of both estimators depend on the estimation of the \code{d}-dimensional tail index \eqn{\gamma}. The \code{d}-dimensional tail index \eqn{\gamma} is estimated using the \code{d}-dimensional Hill estimator (\code{tailest='Hill'}), see \link{MultiHTailIndex}). See Section 2.2 in Padoan and Stupfler (2020) for details.
		\item If \code{bias=TRUE} then \code{d}-dimensional \eqn{\gamma} is estimated using formula (4.2) of Haan et al. (2016). This is used by the LAWS and QB estimators. Furthermore, the \eqn{\tau'_n}--\emph{th} quantile is estimated using the formula in page 330 of de Haan et al. (2016). This provides a bias corrected version of the Weissman estimator. This is used by the QB estimator.
		However, in this case the asymptotic variance is not estimated using the formula in Haan et al. (2016) Theorem 4.2. Instead, for simplicity the asymptotic variance-covariance matrix is estimated by the formulas Section 3.2 of Padoan and Stupfler (2020).
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, for each marginal distribution when \code{tau=NULL} and \code{method='LAWS'} or \code{method='QB'}, then \eqn{\tau_n=1-k_n/n} is the intermediate level of the expectile to be stimated. When \code{tailest='Hill'}, for each marginal distributions, then \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics used in the definition of the Hill estimator.
		\item A small value \eqn{\alpha\in (0,1)} specifies the significance level of Wald-type hypothesis testing.}
}

\value{
  A list with elements:
    \itemize{
	  \item \code{logLikR}: the observed value of log-likelihood ratio statistic test;
      \item \code{critVal}: the quantile (critical level) of a chi-square distribution with \code{d} degrees of freedom and confidence level \eqn{\alpha}.}
}

\references{
Padoan A.S. and Stupfler, G. (2020). Joint inference on extreme expectiles for multivariate
heavy-tailed distributions. \emph{arXiv e-prints} arXiv:2007.08944, \url{https://arxiv.org/abs/2007.08944}
}

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://mypage.unibocconi.it/simonepadoan/};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{MultiHTailIndex},  \link{predMultiExpectiles}, \link{extMultiQuantile}
}

\examples{
# Hypothesis testing on the equality extreme expectiles based on a sample of
# d-dimensional observations simulated from a joint distribution with
# a Gumbel copula and equal Frechet marginal distributions.
library(plot3D)
library(copula)
library(evd)

# distributional setting
copula <- "Gumbel"
dist <- "Frechet"

# parameter setting
dep <- 3
dim <- 3
scale <- rep(1, dim)
shape <- rep(3, dim)
par <- list(dep=dep, scale=scale, shape=shape, dim=dim)

# Intermediate level (or sample tail probability 1-tau)
tau <- 0.95
# Extreme level (or tail probability 1-tau1 of unobserved expectile)
tau1 <- 0.9995

# sample size
ndata <- 1000

# Simulates a sample from a multivariate distribution with equal Frechet
# marginals distributions and a Gumbel copula
data <- rmdata(ndata, dist, copula, par)
scatter3D(data[,1], data[,2], data[,3])

# Performs Wald-type hypothesis testing
HypoTesting(data, tau, tau1)

# Hypothesis testing on the equality extreme expectiles based on a sample of
# d-dimensional observations simulated from a joint distribution with
# a Clayton copula and different Frechet marginal distributions.

# distributional setting
copula <- "Clayton"
dist <- "Frechet"

# parameter setting
dim <- 3
dep <- 2
scale <- rep(1, dim)
shape <- c(2.1, 3, 4.5)
par <- list(dep=dep, scale=scale, shape=shape, dim=dim)

# Intermediate level (or sample tail probability 1-tau)
tau <- 0.95
# Extreme level (or tail probability 1-tau1 of unobserved expectile)
tau1 <- 0.9995

# sample size
ndata <- 1000

# Simulates a sample from a multivariate distribution with equal Frechet
# marginals distributions and a Gumbel copula
data <- rmdata(ndata, dist, copula, par)
scatter3D(data[,1], data[,2], data[,3])

# Performs Wald-type hypothesis testing
HypoTesting(data, tau, tau1)
}
