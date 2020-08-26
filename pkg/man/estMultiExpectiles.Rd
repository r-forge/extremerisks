\name{estMultiExpectiles}
\alias{estMultiExpectiles}

\title{Multidimensional High Expectile Estimation}
\description{Computes point estimates and \eqn{(1-\alpha)100\%} confidence regions for \code{d}-dimensional expectiles at the intermediate level.}
\usage{
estMultiExpectiles(data, tau, method="LAWS", tailest="Hill", var=FALSE,
                   varType="asym-Ind-Adj", k=NULL, alpha=0.05, plot=FALSE)
}

\arguments{
	\item{data}{A matrix of \eqn{(n \times d)}{(n x d)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}.}
	\item{method}{A string specifying the method used to estimate the expecile. By default \code{est="LAWS"} specifies the use of the direct LAWS estimator. See \bold{Details}.}
	\item{tailest}{A string specifying the type of tail index estimator. By default \code{tailest="Hill"} specifies the use of Hill estimator. See \bold{Details}.}
	\item{var}{If \code{var=TRUE} then an estimate of the variance of the expectile estimator is computed.}
	\item{varType}{A string specifying the asymptotic variance-covariance matrix to compute. By default \code{varType="asym-Ind-Adj"} specifies that the variance-covariance matrix is computed assuming dependent variables and exploiting a suitable adjustment. See \bold{Details}.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence region for the \code{d}-dimensional expecile at the intermedite level.}
    \item{plot}{A logical value. By default \code{plot=FALSE} specifies that no graphical representation of the estimates is not provided. See \bold{Details}.}
}

\details{
	For a dataset \code{data} of \code{d}-dimensional observations and sample size \eqn{n}, an estimate of the \eqn{\tau_n}-\emph{th} \code{d}-dimensional is computed. Two estimators are available: the so-called direct Least Asymmetrically Weighted Squares (LAWS) and indirect Quantile-Based (QB). The QB estimator depends on the estimation of the \code{d}-dimensional tail index \eqn{\gamma}. Here, \eqn{\gamma} is estimated using the Hill estimator (see \link{MultiHTailIndex}). The data are regarded as \code{d}-dimensional temporal independent observations coming from dependent variables. See Padoan and Stupfler (2020) for details.
	\itemize{
		\item The so-called intermediate level \code{tau} or \eqn{\tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. Practically, for each individual marginal distribution \eqn{\tau_n \in (0,1)}{\tau_n in (0,1)} is the ratio between \emph{N} (Numerator) and \emph{D} (Denominator). Where \emph{N} is the empirical mean distance of the \eqn{\tau_n}-\emph{th} expectile from the observations smaller than it, and \emph{D} is the empirical mean distance of \eqn{\tau_n}-\emph{th} expectile from all the observations.
		\item If \code{method='LAWS'}, then the expectile at the intermediate level \eqn{\tau_n} is estimated applying the direct LAWS estimator. Instead, If \code{method='QB'} the indirect QB esimtator is used to estimate the expectile. See Section 2.1 in Padoan and Stupfler (2020) for details.
		\item When the expectile is estimated by the indirect QB esimtator (\code{method='QB'}), an estimate of the \code{d}-dimensional tail index \eqn{\gamma} is needed. Here the \code{d}-dimensional tail index \eqn{\gamma} is estimated using the \code{d}-dimensional Hill estimator (\code{tailest='Hill'}, see \link{MultiHTailIndex}). This is the only available option so far (soon more results will be available).
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, for each marginal distribution, when \code{method='LAWS'} and \code{tau=NULL}, \eqn{k_n} specifies by \eqn{\tau_n=1-k_n/n}{tau_n = 1 - k_n / n} the intermediate level of the expectile. Instead, for each marginal distribution, when \code{method='QB'}, then the value \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics to be used to estimate \eqn{\gamma} by the Hill estimator and if \code{tau=NULL} then it also specifies by \eqn{\tau_n=1-k_n/n} the confidence level \eqn{\tau_n} of the quantile to estimate.
		\item If \code{var=TRUE} then an estimate of the asymptotic variance-covariance matrix of the \code{d}-dimensional expecile estimator is computed. If the data are regarded as \code{d}-dimensional temporal independent observations coming from dependent variables. Then, the asymptotic variance-covariance matrix is estimated by the formulas in section 3.1 of Padoan and Stupfler (2020). In particular, the variance-covariance matrix is computed exploiting the asymptotic behaviour of the relative explectile estimator appropriately normalized and using a suitable adjustment. This is achieved through \code{varType="asym-Ind-Adj"}. The data can also be regarded as code{d}-dimensional temporal independent observations coming from independent variables. In this case the asymptotic variance-covariance matrix is diagonal and is also computed exploiting the formulas in section 3.1 of Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Ind"}.
		\item Given a small value \eqn{\alpha\in (0,1)} then an asymptotic confidence region for the \eqn{\tau_n}-\emph{th} expectile, with approximate nominal confidence level \eqn{(1-\alpha)100\%} is computed. In particular, a "symmetric" confidence regions is computed exploiting the asymptotic behaviour of the relative explectile estimator appropriately normalized. See Sections 3.1 of Padoan and Stupfler (2020) for detailed.
        \item If \code{plot=TRUE} then a graphical representation of the estimates is not provided.}
}

\value{
  A list with elements:
    \itemize{
	  \item \code{ExpctHat}: an point estimate of the \eqn{\tau_n}-\emph{th} \code{d}-dimensional expecile;
      \item \code{biasTerm}: an point estimate of the bias term of the estimated expecile;
	  \item \code{VarCovEHat}: an estimate of the asymptotic variance of the expectile estimator;
	  \item \code{EstConReg}: an estimate of the approximate \eqn{(1-\alpha)100\%} confidence region for \eqn{\tau_n}-\emph{th} \code{d}-dimensional expecile.}
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
# Extreme expectile estimation at the intermediate level tau obtained with
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
tau <- .95

# sample size
ndata <- 1000

# Simulates a sample from a multivariate distribution with equal Frechet
# marginals distributions and a Gumbel copula
data <- rmdata(ndata, dist, copula, par)
scatter3D(data[,1], data[,2], data[,3])

# High d-dimensional expectile (intermediate level) estimation
expectHat <- estMultiExpectiles(data, tau, var=TRUE)
expectHat$ExpctHat
expectHat$VarCovEHat
# run the following command to see the graphical representation
\donttest{
 expectHat <- estMultiExpectiles(data, tau, var=TRUE, plot=TRUE)
}
}
