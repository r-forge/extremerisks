\name{estExtLevel}
\alias{estExtLevel}

\title{Extreme Level Estimation}
\description{Estimates the expectile's extreme level corresponding to a quantile's extreme level.}
\usage{
estExtLevel(alpha_n, data=NULL, gammaHat=NULL, VarGamHat=NULL, tailest="Hill", k=NULL,
            var=FALSE, varType="asym-Dep", bigBlock=NULL, smallBlock=NULL, alpha=0.05)
}

\arguments{
	\item{alpha_n}{A real in \eqn{(0,1)} specifying the extreme level \eqn{\alpha_n} for the quantile. See \bold{Details}.}
    \item{data}{A vector of \eqn{(1 \times n)}{(1 x n)} observations to be used to estimate the tail index in the case it is not provided. By default \code{data=NULL} specifies that no data are given.}
    \item{gammaHat}{A real specifying an estimate of the tail index. By default \code{gammaHat=NULL} specifies that no estimate is given. See \bold{Details}.}
    \item{VarGamHat}{A real specifying an estimate of the variance of the tail index estimate. By default \code{VarGamHat=NULL} specifies that no estimate is given. See \bold{Details}.}
	\item{tailest}{A string specifying the type of tail index estimator to be used. By default \code{tailest="Hill"} specifies the use of Hill estimator. See \bold{Details}.}
    \item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
	\item{var}{If \code{var=TRUE} then an estimate of the variance of the extreme level estimator is computed.}
	\item{varType}{A string specifying the asymptotic variance to compute. By default \code{varType="asym-Dep"} specifies the variance estimator for serial dependent observations. See \bold{Details}.}
	\item{bigBlock}{An interger specifying the size of the big-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{smallBlock}{An interger specifying the size of the small-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence interval for the expecile at the intermedite level.}
}

\details{
	For a given extreme level \eqn{\alpha_n} for the \eqn{\alpha_n}-\emph{th} quantile, an estimate of the extreme level \eqn{\tau_n'(\alpha_n)} is computed such that \eqn{\xi_{\tau_n'(\alpha_n)}=q_{\alpha_n}}. The estimator is defined by

    \eqn{\hat{\tau}_n'(\alpha_n) = 1 - (1 - \alpha_n)\frac{\hat{\gamma}_n}{1-\hat{\gamma}_n}}

    where \eqn{\hat{\gamma}_n} is a consistent estimator of the tail index \eqn{\gamma}. If a value for the parameter \code{gammaHat} is given, then such a value is used to compute \eqn{\hat{\tau}_n'}. If \code{gammaHat} is \code{NULL} and a dataset is provided through the parameter \code{data}, then the tail index \eqn{\gamma} is estimated by a suitable estimator \eqn{\hat{\gamma}_n}. See Section 6 in Padoan and Stupfler (2020) for more details.
	\itemize{
		\item If \code{VarGamHat} is specified, i.e. the variance of the tail index estimator, then the variance of the extreme level estimator \eqn{\hat{\tau}_n'} is computed by using such value.
		\item When estimating the tail index, if \code{tailest='Hill'} then \eqn{\gamma} is estimated using the Hill estimator (see also \link{HTailIndex}). If \code{tailest='ML'} then \eqn{\gamma} is estimated using the Maximum Likelihood estimator (see \link{MLTailIndex}).
        If \code{tailest='ExpBased'} then \eqn{\gamma} is estimated using the expectile based estimator (see \link{EBTailIndex}).
        If \code{tailest='Moment'} then \eqn{\gamma} is estimated using the moment based estimator (see \link{MomTailIndex}). See Padoan and Stupfler (2020) for details.
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, when \code{tailest="Hill"} then the value \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics to be used to estimate \eqn{\gamma} by the Hill estimator. See \link{MLTailIndex}, \link{EBTailIndex} and \link{MomTailIndex} for the other estimators.
		\item If \code{var=TRUE} then the asymptotic variance of the extreme level estimator is computed by applying the delta method, i.e.

        \eqn{Var(\tau_n') = Var(\hat{\gamma}_n) * (\alpha_n-1)^2 / (1-\hat{\gamma}_n)^4}

        where \eqn{Var(\hat{\gamma}_n} is provided by \code{VarGamHat} or is estimated when esitmating the tail index through \code{tailest='Hill'} and \code{tailest='ML'}. See  \link{HTailIndex} and \link{MLTailIndex} for details on how the variance is computed.
		\item Given a small value \eqn{\alpha\in (0,1)} then an asymptotic confidence interval for the extreme level, \eqn{\tau_n'(\alpha_n)}, with approximate nominal confidence level \eqn{(1-\alpha)100\%} is computed.
	}
}

\value{
  A list with elements:
    \itemize{
	  \item \code{tauHat}: an estimate of the extreme level \eqn{\tau_n'};
	  \item \code{tauVar}: an estimate of the asymptotic variance of the extreme level estimator \eqn{\hat{\tau}_n'(\alpha_n)};
	  \item \code{tauCI}: an estimate of the approximate \eqn{(1-\alpha)100\%} confidence interval for the extreme level \eqn{\tau_n'(\alpha_n)}.
	}
}

\references{
Padoan A.S. and Stupfler, G. (2020). Extreme expectile estimation for heavy-tailed time series. \emph{arXiv e-prints} arXiv:2004.04078, \url{https://arxiv.org/abs/2004.04078}.

Daouia, A., Girard, S. and Stupfler, G. (2018). Estimation of tail risk based on extreme expectiles. \emph{Journal of the Royal Statistical Society: Series B}, \bold{80}, 263-292.

}

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://mypage.unibocconi.it/simonepadoan/};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{estExpectiles}, \link{predExpectiles}, \link{extQuantile}
}

\examples{
# Extreme level estimation for a given quantile's extreme level alpha_n
# obtained with 1-dimensional data simulated from an AR(1) with Student-t innovations

tsDist <- "studentT"
tsType <- "AR"

# parameter setting
corr <- 0.8
df <- 3
par <- c(corr, df)

# Big- small-blocks setting
bigBlock <- 65
smallBlock <- 15

# quantile's extreme level
alpha_n <- 0.999

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rtimeseries(ndata, tsDist, tsType, par)

# expectile's extreme level estimation
tau1Hat <- estExtLevel(alpha_n, data, var=TRUE, k=150, bigBlock=bigBlock,
                       smallBlock=smallBlock)
tau1Hat
}
