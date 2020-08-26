\name{EBTailIndex}
\alias{EBTailIndex}

\title{Expectile Based Tail Index Estimation}
\description{Computes a point estimate of the tail index based on the Expectile Based (EB) estimator.}
\usage{
EBTailIndex(data, tau, est=NULL)
}

\arguments{
	\item{data}{A vector of \eqn{(1 \times n)}{(1 x n)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}\.}
	\item{est}{A real specifying the estimate of the expectile at the intermediate level \code{tau}.}
}

\details{
	For a dataset \code{data} of sample size \eqn{n}, the tail index \eqn{\gamma} of its (marginal) distribution is estimated using the EB estimator:

    \eqn{
    \hat{\gamma}_n^E =\left(1+\frac{\hat{\bar{F}}_n(\tilde{\xi}_{\tau_n})}{1-\tau_n}\right)^{-1}
	}{\gamma_n^E=(1+\frac{hat{bar{F}}_n(tilde{xi}_{tau_n})}{1-tau_n})^{-1}},

	where \eqn{\hat{\bar{F}}_n}{\hat{\bar{F}}_n} is the empirical survival function of the observations, \eqn{\tilde{\xi}_{\tau_n}}{tilde{xi}_{tau_n}} is an estimate of the \eqn{\tau_n}-\emph{th} expectile.
	The observations can be either independent or temporal dependent. See Padoan and Stupfler (2020) and Daouia et al. (2018) for details.
	\itemize{
	    \item The so-called intermediate level \code{tau} or \eqn{\tau_n}{tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. Practically, \eqn{\tau_n \in (0,1)}{\tau_n in (0,1)} is the ratio between the empirical mean distance of the \eqn{\tau_n}-\emph{th} expectile from the smaller observations and the empirical mean distance of of the \eqn{\tau_n}-\emph{th} expectile from all the observations. An estimate of \eqn{\tau_n}-\emph{th} expectile is computed and used in turn to estimate \eqn{\gamma}.
		\item The value \code{est}, if provided, is meant to be an esitmate of the \eqn{\tau_n}-\emph{th} expectile which is used to estimate \eqn{\gamma}. On the contrary, if \code{est=NULL}, then the routine \code{EBTailIndex} estimate first the \eqn{\tau_n}-\emph{th} expectile expectile and then use it to estimate \eqn{\gamma}.
	}
}

\value{
	An estimate of the tain index \eqn{\gamma}.
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
	\link{HTailIndex}, \link{MomTailIndex}, \link{MLTailIndex},
}

\examples{
# Tail index estimation based on the Expectile based estimator obtained with data
# simulated from an AR(1) with 1-dimensional Student-t distributed innovations

tsDist <- "studentT"
tsType <- "AR"

# parameter setting
corr <- 0.8
df <- 3
par <- c(corr, df)

# Big- small-blocks setting
bigBlock <- 65
smallblock <- 15

# Intermediate level (or sample tail probability 1-tau)
tau <- 0.97

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rtimeseries(ndata, tsDist, tsType, par)

# tail index estimation
gammaHat <- EBTailIndex(data, tau)
gammaHat
}
