\name{predMultiExpectiles}
\alias{predMultiExpectiles}

\title{Multidimensional Extreme Expectile Estimation}
\description{Computes point estimates and \eqn{(1-\alpha)100\%} confidence regions for \code{d}-dimensional expectile at the extreme level (Expectile Prediction).}
\usage{
predMultiExpectiles(data, tau, tau1, method="LAWS", tailest="Hill", var=FALSE,
                    varType="asym-Ind-Adj-Log", bias=FALSE, k=NULL, alpha=0.05,
                    plot=FALSE)
}
\arguments{
	\item{data}{A matrix of \eqn{(n \times d)}{(n x d)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}.}
	\item{tau1}{A real in \eqn{(0,1)} specifying the extreme level \eqn{\tau'_n}. See \bold{Details}.}
	\item{method}{A string specifying the method used to estimate the expecile. By default \code{est="LAWS"} specifies the use of the LAWS based estimator. See \bold{Details}.}
	\item{tailest}{A string specifying the tail index estimator. By default \code{tailest="Hill"} specifies the use of Hill estimator. See \bold{Details}.}
	\item{var}{If \code{var=TRUE} then an estimate of the asymptotic variance of the expectile estimator is computed.}
	\item{varType}{A string specifying the type of asymptotic variance-covariance matrix to compute. By default \code{varType="asym-Ind-Adj-Log"} specifies that the variance-covariance matrix is computed assuming dependent variables and exploiting the log scale and a suitable adjustment. See \bold{Details}.}
	\item{bias}{A logical value. By default \code{bias=FALSE} specifies that no bias correction is computed. See \bold{Details}.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence region for the \code{d}-dimensional expecile at the extreme level.}
    \item{plot}{A logical value. By default \code{plot=FALSE} specifies that no graphical representation of the estimates is provided. See \bold{Details}.}
}

\details{
	For a dataset \code{data} of \code{d}-dimensional observations and sample size \eqn{n}, an estimate of the \eqn{\tau'_n}-\emph{th} \code{d}-dimensional expectile is computed. The estimation of the \code{d}-dimensional expectile at the extreme level \code{tau1} (\eqn{\tau'_n}) is meant to be a prediction beyond the observed sample.  Two estimators are available: the so-called Least Asymmetrically Weighted Squares (LAWS) based estimator and the Quantile-Based (QB) estimator. The definition of both estimators depends on the estimation of the \code{d}-dimensional tail index \eqn{\gamma}. Here, \eqn{\gamma} is estimated using the Hill estimation (see \link{MultiHTailIndex} for details).
	The data are regarded as \code{d}-dimensional temporal independent observations coming from dependent variables. See Padoan and Stupfler (2020) for details.
	\itemize{
		\item The so-called intermediate level \code{tau} or \eqn{\tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. Practically, for each marginal distribution, \eqn{\tau_n \in (0,1)}{\tau_n in (0,1)} is the ratio between \emph{N} (Numerator) and \emph{D} (Denominator). Where \emph{N} is the empirical mean distance of the \eqn{\tau_n}-\emph{th} expectile from the observations smaller than it, and \emph{D} is the empirical mean distance of \eqn{\tau_n}-\emph{th} expectile from all the observations.
		\item The so-called extreme level \code{tau1} or \eqn{\tau'_n} is a sequence of positive reals such that \eqn{\tau'_n \to 1}{\tau'_n -> 1} as \eqn{n \to \infty}{n -> \infty}.
		For each marginal distribution, the value \eqn{(1-tau'_n) \in (0,1)}{(1-tau'_n) in (0,1)} is meant to be a small tail probability such that \eqn{(1-\tau'_n)=1/n} or \eqn{(1-\tau'_n) < 1/n}. It is also assumed that \eqn{n(1-\tau'_n) \to C}{n(1-\tau'_n) -> C} as \eqn{n \to \infty}{n -> \infty}, where \eqn{C} is a positive finite constant. Typically, \eqn{C \in (0,1)}{C in (0,1)} so it is expected that there are no observations in a data sample that are greater than the expectile at the extreme level \eqn{\tau_n'}.
		\item When \code{method='LAWS'}, then the \eqn{\tau'_n}-\emph{th} \code{d}-dimensional expectile is estimated using the LAWS based estimator. When \code{method='QB'}, the expectile is instead estimated using the QB esimtator. The definition of both estimators depend on the estimation of the \code{d}-dimensional tail index \eqn{\gamma}. The \code{d}-dimensional tail index \eqn{\gamma} is estimated using the \code{d}-dimensional Hill estimator (\code{tailest='Hill'}), see \link{MultiHTailIndex}). This is the only available option so far (soon more results will be available). See Section 2.2 in Padoan and Stupfler (2020) for details.
		\item If \code{var=TRUE} then an estimate of the asymptotic variance-covariance matrix of the \eqn{tau'_n}-\emph{th} \code{d}-dimensional expectile is computed. Notice that the estimation of the asymptotic variance-covariance matrix \bold{is only available} when \eqn{\gamma} is estimated using the Hill estimator (see \link{MultiHTailIndex}). The data are regarded as temporal independent observations coming from dependent variables. The asymptotic variance-covariance matrix is estimated exploiting the formulas in Section 3.2 of Padoan and Stupfler (2020). The variance-covariance matrix is computed exploiting the asymptotic behaviour of the normalized expectile estimator which is  expressed in logarithmic scale. In addition, a suitable adjustment is considered. This is achieved through \code{varType="asym-Ind-Adj-Log"}.  The data can also be regarded as code{d}-dimensional temporal independent observations coming from independent variables. In this case the asymptotic variance-covariance matrix is diagonal and is also computed exploiting the formulas in Section 3.2 of Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Ind-Log"}. If \code{varType="asym-Ind-Adj"}, then the variance-covariance matrix is computed exploiting the asymptotic behaviour of the relative expectile estimator appropriately normalized and exploiting a suitable adjustment. This concerns the case of dependent variables. The case of independent variables is achieved through \code{varType="asym-Ind"}.
		\item If \code{bias=TRUE} then \code{d}-dimensional \eqn{\gamma} is estimated using formula (4.2) of Haan et al. (2016). This is used by the LAWS and QB estimators. Furthermore, the \eqn{\tau'_n}--\emph{th} quantile is estimated using the formula in page 330 of de Haan et al. (2016). This provides a bias corrected version of the Weissman estimator. This is used by the QB estimator.
		However, in this case the asymptotic variance is not estimated using the formula in Haan et al. (2016) Theorem 4.2. Instead, for simplicity the asymptotic variance-covariance matrix is estimated by the formulas Section 3.2 of Padoan and Stupfler (2020).
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, for each marginal distribution when \code{tau=NULL} and \code{method='LAWS'} or \code{method='QB'}, then \eqn{\tau_n=1-k_n/n} is the intermediate level of the expectile to be stimated. When \code{tailest='Hill'}, for each marginal distributions, then \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics used in the definition of the Hill estimator.
		\item Given a small value \eqn{\alpha\in (0,1)} then an estimate of an asymptotic confidence region for \eqn{tau'_n}-\emph{th} \code{d}-dimensional expectile, with approximate nominal confidence level \eqn{(1-\alpha)100\%}, is computed. The confidence regions are computed exploiting the formulas in Section 3.2 of Padoan and Stupfler (2020). If \code{varType="asym-Ind-Adj-Log"}, then an "asymmetric" confidence regions is computed exploiting the asymptotic behaviour of the normalized expectile estimator in logarithmic scale and using a suitable adjustment. This choice is recommended. If \code{varType="asym-Ind-Adj"}, then the a "symmetric" confidence regions is computed exploiting the asymptotic behaviour of the relative explectile estimator appropriately normalized.
        \item If \code{plot=TRUE} then a graphical representation of the estimates is not provided.}
}

\value{
  A list with elements:
    \itemize{
	  \item \code{ExpctHat}: an estimate of the \eqn{\tau'_n}-\emph{th} \code{d}-dimensional expecile;
      \item \code{biasTerm}: an estimate of the bias term of yje \eqn{\tau'_n}-\emph{th} \code{d}-dimensional expecile;
	  \item \code{VarCovEHat}: an estimate of the asymptotic variance-covariance of the \code{d}-dimensional expectile estimator;
	  \item \code{EstConReg}: an estimate of the approximate \eqn{(1-\alpha)100\%} confidence regions for \eqn{\tau'_n}-\emph{th} \code{d}-dimensional expecile.}
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
	\link{MultiHTailIndex},  \link{estMultiExpectiles}, \link{extMultiQuantile}
}

\examples{
# Extreme expectile estimation at the extreme level tau1 obtained with
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

# High d-dimensional expectile (intermediate level) estimation
expectHat <- predMultiExpectiles(data, tau, tau1, var=TRUE)

expectHat$ExpctHat
expectHat$VarCovEHat
# run the following command to see the graphical representation
# expectHat <- predMultiExpectiles(data, tau, tau1, var=TRUE, plot=TRUE)
}
