\name{extMultiQuantile}
\alias{extMultiQuantile}

\title{Multidimensional Value-at-Risk (VaR) or Extreme Quantile (EQ) Estimation}
\description{Computes point estimates and \eqn{(1-\alpha)100\%} confidence regions for \code{d}-dimensional VaR based on the Weissman estimator.}
\usage{
extMultiQuantile(data, tau, tau1, var=FALSE, varType="asym-Ind-Log", bias=FALSE,
                 k=NULL, alpha=0.05, plot=FALSE)
}

\arguments{
	\item{data}{A matrix of \eqn{(n \times d)}{(n x d)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}.}
	\item{tau1}{A real in \eqn{(0,1)} specifying the extreme level \eqn{\tau'_n}. See \bold{Details}.}
	\item{var}{If \code{var=TRUE} then an estimate of the asymptotic variance-covariance matrix of the \code{d}-dimensional VaR estimator is computed.}
	\item{varType}{A string specifying the type of asymptotic variance-covariance matrix to compute. By default \code{varType="asym-Ind-Log"} specifies that the variance-covariance matrix is obtained assuming dependent variables and exploiting the logarithmic scale. See \bold{Details}.}
	\item{bias}{A logical value. By default \code{biast=FALSE} specifies that no bias correction is computed. See \bold{Details}.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence region for the \code{d}-dimensional VaR.}
    \item{plot}{A logical value. By default \code{plot=FALSE} specifies that no graphical representation of the estimates is not provided. See \bold{Details}.}
}

\details{
	For a dataset \code{data} of \code{d}-dimensional observations and sample size \eqn{n}, the VaR or EQ, correspoding to the extreme level \code{tau1}, is computed by applying the \code{d}-dimensional Weissman estimator. The definition of the Weissman estimator depends on the estimation of the \code{d}-dimensional tail index \eqn{\gamma}. Here, \eqn{\gamma} is estimated using the Hill estimation (see \link{MultiHTailIndex}). The data are regarded as \code{d}-dimensional temporal independent observations coming from dependent variables. See Padoan and Stupfler (2020) for details.
	\itemize{
		\item The so-called intermediate level \code{tau} or \eqn{\tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. Practically, for each variable, \eqn{(1-\tau_n)\in (0,1)}{(1-\tau_n) in (0,1)} is a small proportion of observations in the observed data sample that exceed the \eqn{tau_n}-\emph{th} empirical quantile. Such proportion of observations is used to estimate the individual \eqn{tau_n}-\emph{th} quantile and tail index \eqn{\gamma}.
		\item The so-called extreme level \code{tau1} or \eqn{\tau'_n} is a sequence of positive reals such that \eqn{\tau'_n \to 1}{\tau'_n -> 1} as \eqn{n \to \infty}{n -> \infty}.
		For each variable, the value \eqn{(1-tau'_n) \in (0,1)}{(1-\tau'_n) in (0,1)} is meant to be a small tail probability such that \eqn{(1-\tau'_n)=1/n} or \eqn{(1-\tau'_n) < 1/n}. It is also assumed that \eqn{n(1-\tau'_n) \to C}{n(1-tau'_n) -> C} as \eqn{n \to \infty}{n -> \infty}, where \eqn{C} is a positive finite constant. The value \eqn{C} is the expected number of exceedances of the individual \eqn{\tau'_n}-\emph{th} quantile. Typically, \eqn{C \in (0,1)}{C in (0,1)} which means that it is expected that there are no observations in a data sample exceeding the individual quantile of level \eqn{(1-\tau_n')}.
		\item If \code{var=TRUE} then an estimate of the asymptotic variance-covariance matrix of the \eqn{tau'_n}-\emph{th} \code{d}-dimensional quantile is computed. The data are regarded as temporal independent observations coming from dependent variables. The asymptotic variance-covariance matrix is estimated exploiting the formula in Section 5 of Padoan and Stupfler (2020). In particular, the variance-covariance matrix is computed exploiting the asymptotic behaviour of the normalized quantile estimator which is expressed in logarithmic scale. This is achieved through \code{varType="asym-Ind-Log"}. If \code{varType="asym-Ind"} then the variance-covariance matrix is computed exploiting the asymptotic behaviour of the \code{d}-dimensional relative quantile estimator appropriately normalized (see formula in Section 5 of Padoan and Stupfler (2020)).
		\item If \code{bias=TRUE} then an estimate of each individual \eqn{\tau'_n}--\emph{th} quantile is estimated using the formula in page 330 of de Haan et al. (2016), which provides a bias corrected version of the Weissman estimator. However, in this case the asymptotic variance is not estimated using the formula in Haan et al. (2016) Theorem 4.2. For simplicity standard the variance-covariance matrix is still computed using formula in Section 5 of Padoan and Stupfler (2020).
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, for each marginal distribution, the value \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics to be used to estimate the individual \eqn{\tau_n}-\emph{th} empirical quantile and individual tail index \eqn{\gamma_j} for \eqn{j=1,\ldots,d}{j=1,...,d}. The intermediate level \eqn{\tau_n} can be seen defined as \eqn{\tau_n=1-k_n/n}.
        \item Given a small value \eqn{\alpha\in (0,1)} then an estimate of an asymptotic confidence region for \eqn{tau'_n}-\emph{th} \code{d}-dimensional quantile, with approximate nominal confidence level \eqn{(1-\alpha)100\%}, is computed. The confidence regions are computed exploiting the asymptotic behaviour of the normalized quantile estimator in logarithmic scale. This is an "asymmetric" region and it is achieved through \code{varType="asym-Ind-Log"}. A "symmetric" region is obtained exploiting the asymptotic behaviour of the relative quantile estimator appropriately normalized, see formula in Section 5 of Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Ind"}.
        \item If \code{plot=TRUE} then a graphical representation of the estimates is not provided.}
}

\value{
	A list with elements:
	\itemize{
		\item \code{ExtQHat}: an estimate of the \code{d}-dimensional VaR or \eqn{\tau'_n}-\emph{th} \code{d}-dimensional quantile;
		\item \code{VarCovExQHat}: an estimate of the asymptotic variance-covariance of the \code{d}-dimensional VaR estimator;
		\item \code{EstConReg}: an estimate of the approximate \eqn{(1-\alpha)100\%} confidence regions for the \code{d}-dimensional VaR.
	}
}

\references{
  Padoan A.S. and Stupfler, G. (2020). Joint inference on extreme expectiles for multivariate
  heavy-tailed distributions. \emph{arXiv e-prints} arXiv:2007.08944, \url{https://arxiv.org/abs/2007.08944}

  de Haan, L., Mercadier, C. and Zhou, C. (2016). Adapting extreme value statistics
  to financial time series: dealing with bias and serial dependence. \emph{Finance and Stochastics},
  \bold{20}, 321-354.

  de Haan, L. and Ferreira, A. (2006). Extreme Value Theory: An Introduction. \emph{Springer}-\emph{Verlag}, New York.
 }

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://mypage.unibocconi.it/simonepadoan/};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{MultiHTailIndex},  \link{estMultiExpectiles}, \link{predMultiExpectiles}
}

\examples{
# Extreme quantile estimation at the extreme level tau1 obtained with
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
# Extreme level (or tail probability 1-tau1 of unobserved quantile)
tau1 <- 0.9995

# sample size
ndata <- 1000

# Simulates a sample from a multivariate distribution with equal Frechet
# marginals distributions and a Gumbel copula
data <- rmdata(ndata, dist, copula, par)
scatter3D(data[,1], data[,2], data[,3])

# High d-dimensional expectile (intermediate level) estimation
extQHat <- extMultiQuantile(data, tau, tau1, TRUE)

extQHat$ExtQHat
extQHat$VarCovExQHat
# run the following command to see the graphical representation
\donttest{
 extQHat <- extMultiQuantile(data, tau, tau1, TRUE, plot=TRUE)
}
}
