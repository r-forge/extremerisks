\name{estExpectiles}
\alias{estExpectiles}

\title{High Expectile Estimation}
\description{Computes a point and interval estimate of the expectile at the intermediate level.}
\usage{
estExpectiles(data, tau, method="LAWS", tailest="Hill", var=FALSE, varType="asym-Dep-Adj",
              bigBlock=NULL, smallBlock=NULL, k=NULL, alpha=0.05)
}

\arguments{
	\item{data}{A vector of \eqn{(1 \times n)}{(1 x n)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}.}
	\item{method}{A string specifying the method used to estimate the expecile. By default \code{est="LAWS"} specifies the use of the direct LAWS estimator. See \bold{Details}.}
	\item{tailest}{A string specifying the type of tail index estimator. By default \code{tailest="Hill"} specifies the use of Hill estimator. See \bold{Details}.}
	\item{var}{If \code{var=TRUE} then an estimate of the variance of the expectile estimator is computed.}
	\item{varType}{A string specifying the asymptotic variance to compute. By default \code{varType="asym-Dep-Adj"} specifies the variance estimator for serial dependent observations implemented with a suitable adjustment. See \bold{Details}.}
	\item{bigBlock}{An interger specifying the size of the big-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{smallBlock}{An interger specifying the size of the small-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence interval for the expecile at the intermedite level.}
}

\details{
	For a dataset \code{data} of sample size \eqn{n}, an estimate of the \eqn{\tau_n}-\emph{th} expectile is computed. Two estimators are available: the so-called direct Least Asymmetrically Weighted Squares (LAWS) and indirect Quantile-Based (QB). The definition of the QB estimator depends on the estimation of the tail index \eqn{\gamma}. Here, \eqn{\gamma} is estimated using the Hill estimation (see \link{HTailIndex}) or in alternative using the the expectile based estimator (see \link{EBTailIndex}). The observations can be either independent or temporal dependent. See Padoan and Stupfler (2020) and Daouia et al. (2018) for details.
	\itemize{
		\item The so-called intermediate level \code{tau} or \eqn{\tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. Practically, \eqn{\tau_n \in (0,1)}{\tau_n in (0,1)} is the ratio between \emph{N} (Numerator) and \emph{D} (Denominator). Where \emph{N} is the empirical mean distance of the \eqn{\tau_n}-\emph{th} expectile from the observations smaller than it, and \emph{D} is the empirical mean distance of \eqn{\tau_n}-\emph{th} expectile from all the observations.
		\item If \code{method='LAWS'}, then the expectile at the intermediate level \eqn{\tau_n} is estimated applying the direct LAWS estimator. Instead, If \code{method='QB'} the indirect QB esimtator is used to estimate the expectile. See Padoan and Stupfler (2020) for details.
		\item When the expectile is estimated by the indirect QB esimtator (\code{method='QB'}), an estimate of the tail index \eqn{\gamma} is needed. If \code{tailest='Hill'} then \eqn{\gamma} is estimated using the Hill estimator (see also \link{HTailIndex}). If \code{tailest='ExpBased'} then \eqn{\gamma} is estimated using the expectile based estimator (see \link{EBTailIndex}). See Padoan and Stupfler (2020) for details.
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, when \code{method='LAWS'} and \code{tau=NULL}, \eqn{k_n} specifies by \eqn{\tau_n=1-k_n/n}{tau_n = 1 - k_n / n} the intermediate level of the expectile. Instead, when \code{method='QB'}, if \code{tailest="Hill"} then the value \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics to be used to estimate \eqn{\gamma} by the Hill estimator and if \code{tau=NULL} then it also specifies by \eqn{\tau_n=1-k_n/n} the confidence level \eqn{\tau_n} of the quantile to estimate. Finally, if \code{tailest="ExpBased"} and \code{tau=NULL} then it also specifies by \eqn{\tau_n=1-k_n/n} the intermediate level expectile based esitmator of \eqn{\gamma} (see \link{EBTailIndex}).
		\item If \code{var=TRUE} then the asymptotic variance of the expecile estimator is computed. With independent observations the asymptotic variance is computed by the formula in Theorem 2 of Daouia et al. (2018). This is achieved through \code{varType="asym-Ind"}. With serial dependent observations the asymptotic variance is estimated by the formula in Theorem 3.1 of Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Dep"}. In this latter case the computation of the asymptotic variance is based on the "big blocks seperated by small blocks" techinque which is a standard tools in time series, see Leadbetter et al. (1986). See also Section 4 of Padoan and Stupfler (2020). The size of the big and small blocks are specified by the parameters \code{bigblock} and \code{smallblock}, respectively. Still with serial dependent observations, If \code{varType="asym-Dep-Adj"}, then the asymptotic variance estimated using formula (11) of Padoan and Stupfler (2020).
		\item Given a small value \eqn{\alpha\in (0,1)} then an asymptotic confidence interval for the \eqn{\tau_n}-\emph{th} expectile, with approximate nominal confidence level \eqn{(1-\alpha)100\%} is computed.
	}
}

\value{
  A list with elements:
    \itemize{
	  \item \code{ExpctHat}: an estimate of the \eqn{\tau_n}-\emph{th} expecile;
	  \item \code{VarExpHat}: an estimate of the asymptotic variance of the expectile estimator;
	  \item \code{CIExpct}: an estimate of the approximate \eqn{(1-\alpha)100\%} confidence interval for \eqn{\tau_n}-\emph{th} expecile.
	}
}

\references{
Padoan A. S. and Stupfler, G. (2020). Extreme expectile estimation for heavy-tailed time series. \emph{arXiv e-prints} arXiv:INSERT.

Daouia, A., Girard, S. and Stupfler, G. (2018). Estimation of tail risk based on extreme expectiles. \emph{Journal of the Royal Statistical Society: Series B}, \bold{80}, 263-292.

Leadbetter, M.R., Lindgren, G. and Rootzen, H. (1989). Extremes and related
properties of random sequences and processes. \emph{Springer}.
}

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://faculty.unibocconi.it/simonepadoan};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{HTailIndex},  \link{EBTailIndex}, \link{predExpectiles}, \link{extQuantile}
}

\examples{
# Estimation of the tau-th expectile for the AR(1) with Student-t innovations
tsDist <- "studentT"
tsType <- "AR"

# parameter setting
corr <- 0.8
df <- 3
par <- c(corr, df)

# Big- small-blocks setting
bigBlock <- 65
smallBlock <- 15

# Intermediate level (or sample tail probability 1-tau)
tau <- 0.99

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rtimeseries(ndata, tsDist, tsType, par)

# High expectile (intermediate level) estimation
expectHat <- estExpectiles(data, tau, var=TRUE, bigBlock=bigBlock, smallBlock=smallBlock)
expectHat$ExpctHat
expectHat$CIExpct
}
