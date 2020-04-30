\name{HTailIndex}
\alias{HTailIndex}

\title{Hill Tail Index Estimation}
\description{Computes a point and interval estimate of the tail index based on the Hill's estimator.}
\usage{
HTailIndex(data, k, var=FALSE, varType="asym-Dep", bias=FALSE, bigBlock=NULL,
           smallBlock=NULL, alpha=0.05)
}

\arguments{
	\item{data}{A vector of \eqn{(1 \times n)}{(1 x n)} observations.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
    \item{var}{If \code{var=TRUE} then an estimate of the variance of the tail index estimator is computed.}
    \item{varType}{A string specifying the asymptotic variance to compute. By default \code{varType="asym-Dep"} specifies the variance estimator for serial dependent observations. See \bold{Details}.}
    \item{bias}{A logical value. By default \code{biast=FALSE} specifies that no bias correction is computed. See \bold{Details}.}
    \item{bigBlock}{An interger specifying the size of the big-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{smallBlock}{An interger specifying the size of the small-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence interval for the tail index.}

}

\details{
	For a dataset \code{data} of sample size \eqn{n}, the tail index \eqn{\gamma} of its (marginal) distribution is computed by applying the Hill estimator. The observations can be either independent or temporal dependent.
	\itemize{
        \item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, the value \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics to be used to estimate \eqn{\gamma}.
		\item If \code{var=TRUE} then an estimate of the asymptotic variance of the Hill estimator is computed. With independent observations the asymptotic variance is estimated by the formula \eqn{\hat{\gamma}^2}, see Theorem 3.2.5 of de Haan and Ferreira (2006). This is achieved through \code{varType="asym-Ind"}. With serial dependent observations the asymptotic variance is estimated by the formula in 1288 in Drees (2000). This is achieved through \code{varType="asym-Dep"}. In this latter case the serial dependence is estimated by exploiting the "big blocks seperated by small blocks" techinque which is a standard tools in time series, see Leadbetter et al. (1986). See also formula (11) in Drees (2003). The size of the big and small blocks are specified by the parameters \code{bigBlock} and \code{smallBlock}, respectively.
        \item If \code{bias=TRUE} then an estimate of the bias term of the Hill estimator is computed implementing using formula (4.2) in de Haan et al. (2016). However, in this case the asymptotic variance is not estimated using the formula in Haan et al. (2016) Theorem 4.1. Instead for simplicity standard formulas have been used (see de Haan and Ferreira 2006 Theorem 3.2.5 and Drees 2000 page 1288).
        \item Given a small value \eqn{\alpha\in (0,1)} then an estimate of an asymptotic confidence interval for \eqn{\gamma}, with approximate nominal confidence level \eqn{(1-\alpha)100\%}, is computed. The confidence intervals are computed exploiting the formulas in de Haan and Ferreira (2006) Theorem 3.2.5 and Drees (2000) page 1288. When \code{biast=TRUE} the confidence intervals are computed in the same way but after correcting the tail index estimate by an estimate of the bias term, see formula (4.2) in de Haan et al. (2016) for details.
	}
}

\value{
	A list with elements:
	\itemize{
		\item \code{gammaHat}: an estimate of tail index \eqn{\gamma};
		\item \code{VarGamHat}: an estimate of the asymptotic variance of the Hill estimator;
		\item \code{BiasGamHat}: an estimate of bias term of the Hill estimator;
        \item \code{AdjExtQHat}: the adjustment to correct the Weissman estimator of an extreme quantile.
	}
}

\references{
  Padoan A.S. and Stupfler, G. (2020). Extreme expectile estimation for heavy-tailed time series. \emph{arXiv e-prints} arXiv:2004.04078, \url{http://arxiv.org/abs/2004.04078}.

  de Haan, L., Mercadier, C. and Zhou, C. (2016). Adapting extreme value statistics
  tonancial time series: dealing with bias and serial dependence. \emph{Finance and Stochastics},
  \bold{20}, 321-354.

  de Haan, L. and Ferreira, A. (2006). Extreme Value Theory: An Introduction. \emph{Springer}-\emph{Verlag}, New York.

  Drees, H. (2000). Weighted approximations of tail processes for \eqn{\beta}-mixing random variables.
  \emph{Annals of Applied Probability}, \bold{10}, 1274-1301.

  Leadbetter, M.R., Lindgren, G. and Rootzen, H. (1989). Extremes and related
  properties of random sequences and processes. \emph{Springer}.
}

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://mypage.unibocconi.it/simonepadoan/};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{MLTailIndex}, \link{MomTailIndex}, \link{EBTailIndex}
}

\examples{
# Tail index estimation based on the Hill estimator obtained with
# 1-dimensional data simulated from an AR(1) with univariate Student-t
# distributed innovations

tsDist <- "studentT"
tsType <- "AR"

# parameter setting
corr <- 0.8
df <- 3
par <- c(corr, df)

# Big- small-blocks setting
bigBlock <- 65
smallBlock <- 15

# Number of larger order statistics
k <- 150

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rtimeseries(ndata, tsDist, tsType, par)

# tail index estimation
gammaHat1 <- HTailIndex(data, k, TRUE, bigBlock=bigBlock, smallBlock=smallBlock)
gammaHat1$gammaHat
gammaHat1$CIgamHat

# tail index estimation with bias correction
gammaHat2 <- HTailIndex(data, 2*k, TRUE, bias=TRUE, bigBlock=bigBlock, smallBlock=smallBlock)
gammaHat2$gammaHat-gammaHat2$BiasGamHat
gammaHat2$CIgamHat
}
