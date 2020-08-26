\name{MultiHTailIndex}
\alias{MultiHTailIndex}

\title{Multidimensional Hill Tail Index Estimation}
\description{Computes point estimates and \eqn{(1-\alpha)100\%} confidence regions estimate of \eqn{d}-dimensional tail indices based on the Hill's estimator.}
\usage{
MultiHTailIndex(data, k, var=FALSE, varType="asym-Dep", bias=FALSE,
                alpha=0.05, plot=FALSE)
}

\arguments{
	\item{data}{A matrix of \eqn{(n \times d)}{(n x d)} observations.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
    \item{var}{If \code{var=TRUE} then an estimate of the variance-covariance matrix of the tail indices estimators is computed.}
    \item{varType}{A string specifying the asymptotic variance to compute. By default \code{varType="asym-Dep"} specifies the variance estimator for \eqn{d} dependent marginal variables. See \bold{Details}.}
    \item{bias}{A logical value. By default \code{biast=FALSE} specifies that no bias correction is computed. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence interval for the tail index.}
    \item{plot}{A logical value. By default \code{plot=FALSE} specifies that no graphical representation of the estimates is provided. See \bold{Details}.}
}

\details{
	For a dataset \code{data} of \eqn{(n \times d)}{(n x d)} observations, where \eqn{d} is the number of variables and \eqn{n} is the sample size, the tail index \eqn{\gamma} of the \eqn{d} marginal distributions is estimated by applying the Hill estimator. Together with a point estimate a \eqn{(1-\alpha)100\%} confidence region is computed. The data are regarded as \code{d}-dimensional temporal independent observations coming from dependent variables.
	\itemize{
        \item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, the value \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics to be used to estimate each marginal tail index \eqn{\gamma_j} for \eqn{j=1,\ldots,d}{j=1,...,d}.
		\item If \code{var=TRUE} then an estimate of the asymptotic variance-covariance matrix of the multivariate Hill estimator is computed. With independent observations the asymptotic variance-covariance matrix is estimated by the matrix \eqn{\hat{\Sigma}^{LAWS}_{j,\ell}(\gamma,R)(1,1)}, see bottom formula in page 14 of Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Dep"} which means \eqn{d} dependent marginal variables. When \code{varType="asym-Ind"} \eqn{d} marginal variables are regarded as independent and the returned variance-covariance matrix \eqn{\hat{\Sigma}^{LAWS}_{j,\ell}(\gamma,R)(1,1)} is a diagonal matrix with only variance terms.
        \item If \code{bias=TRUE} then an estimate of the bias term of the Hill estimator is computed implementing using formula (4.2) in de Haan et al. (2016). In this case the asymptotic variance is not estimated using the formula in Haan et al. (2016) Theorem 4.1 but instead for simplicity the formula at the bottom of page 14 in Padoan and Stupfler (2020) is still used.
        \item Given a small value \eqn{\alpha\in (0,1)} then an estimate of an asymptotic confidence region for \eqn{\gamma_j}, for \eqn{j=1,\ldots,d}{j=1,...,d}, with approximate nominal confidence level \eqn{(1-\alpha)100\%}, is computed. The confidence intervals are computed exploiting the asymptotic normality of multivariate Hill estimator appropriately normalized (the logarithmic scale is not used), see Padoan and Stupfler (2020) for details.
        \item If \code{plot=TRUE} then a graphical representation of the estimates is not provided.
	}
}

\value{
	A list with elements:
	\itemize{
		\item \code{gammaHat}: an estimate of the \eqn{d} tail indices \eqn{\gamma_j}, for \eqn{j=1,\ldots,d}{j=1,...,d};
		\item \code{VarCovGHat}: an estimate of the asymptotic variance-covariance matrix of the multivariate Hill estimator;
		\item \code{biasTerm}: an estimate of bias term of the multivariate Hill estimator;
        \item \code{EstConReg}: an estimate of the \eqn{(1-\alpha)100\%} confidence region.
	}
}

\references{
  Padoan A.S. and Stupfler, G. (2020). Joint inference on extreme expectiles for multivariate
heavy-tailed distributions. \emph{arXiv e-prints} arXiv:2007.08944, \url{https://arxiv.org/abs/2007.08944}.

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
	\link{HTailIndex}, \link{rmdata}
}

\examples{
# Tail index estimation based on the multivariate Hill estimator obtained with
# n observations simulated from a d-dimensional random vector with a multivariate
# distribution with equal Frechet margins and a Clayton copula.
library(plot3D)
library(copula)
library(evd)

# distributional setting
copula <- "Clayton"
dist <- "Frechet"

# parameter setting
dep <- 3
dim <- 3
scale <- rep(1, dim)
shape <- rep(3, dim)
par <- list(dep=dep, scale=scale, shape=shape, dim=dim)

# Number of larger order statistics
k <- 150

# sample size
ndata <- 1000

# Simulates a sample from a multivariate distribution with equal Frechet
# marginals distributions and a Clayton copula
data <- rmdata(ndata, dist, copula, par)
scatter3D(data[,1], data[,2], data[,3])

# tail indices estimation
est <- MultiHTailIndex(data, k, TRUE)
est$gammaHat
est$VarCovGHat
# run the following command to see the graphical representation
\donttest{
 est <- MultiHTailIndex(data, k, TRUE, plot=TRUE)
}
}
