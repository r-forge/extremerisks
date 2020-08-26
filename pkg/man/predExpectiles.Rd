\name{predExpectiles}
\alias{predExpectiles}

\title{Extreme Expectile Estimation}
\description{Computes a point and interval estimate of the expectile at the extreme level (Expectile Prediction).}
\usage{
predExpectiles(data, tau, tau1, method="LAWS", tailest="Hill", var=FALSE,
               varType="asym-Dep", bias=FALSE, bigBlock=NULL, smallBlock=NULL,
               k=NULL, alpha_n=NULL, alpha=0.05)
}

\arguments{
	\item{data}{A vector of \eqn{(1 \times n)}{(1 x n)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}.}
	\item{tau1}{A real in \eqn{(0,1)} specifying the extreme level \eqn{\tau'_n}. See \bold{Details}.}
	\item{method}{A string specifying the method used to estimate the expecile. By default \code{est="LAWS"} specifies the use of the LAWS based estimator. See \bold{Details}.}
	\item{tailest}{A string specifying the tail index estimator. By default \code{tailest="Hill"} specifies the use of Hill estimator. See \bold{Details}.}
	\item{var}{If \code{var=TRUE} then an estimate of the asymptotic variance of the expectile estimator is computed.}
	\item{varType}{A string specifying the type of asymptotic variance to compute. By default \code{varType="asym-Dep"} specifies the variance estimator for serial dependent observations. See \bold{Details}.}
	\item{bias}{A logical value. By default \code{bias=FALSE} specifies that no bias correction is computed. See \bold{Details}.}
	\item{bigBlock}{An interger specifying the size of the big-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{smallBlock}{An interger specifying the size of the small-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
    \item{alpha_n}{A real in \eqn{(0,1)} specifying the quantile's extreme level to be use in order to estimate the expectile's extreme level.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence interval for the expecile at the intermedite level.}
}

\details{
	For a dataset \code{data} of sample size \eqn{n}, an estimate of the \eqn{\tau'_n}-\emph{th} expectile is computed. The estimation of the expectile at the extreme level \code{tau1} (\eqn{\tau'_n}) is meant to be a prediction beyond the observed sample.  Two estimators are available: the so-called Least Asymmetrically Weighted Squares (LAWS) based estimator and the Quantile-Based (QB) estimator. The definition of both estimators depends on the estimation of the tail index \eqn{\gamma}. Here, \eqn{\gamma} is estimated using the Hill estimation (see \link{HTailIndex} for details) or in alternative using the the expectile based estimator (see \link{EBTailIndex}).
	The observations can be either independent or temporal dependent. See Section 3.2 in Padoan and Stupfler (2020) for details.
	\itemize{
		\item The so-called intermediate level \code{tau} or \eqn{\tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. Practically, \eqn{\tau_n \in (0,1)}{\tau_n in (0,1)} is the ratio between \emph{N} (Numerator) and \emph{D} (Denominator). Where \emph{N} is the empirical mean distance of the \eqn{\tau_n}-\emph{th} expectile from the observations smaller than it, and \emph{D} is the empirical mean distance of \eqn{\tau_n}-\emph{th} expectile from all the observations.
		\item The so-called extreme level \code{tau1} or \eqn{\tau'_n} is a sequence of positive reals such that \eqn{\tau'_n \to 1}{\tau'_n -> 1} as \eqn{n \to \infty}{n -> \infty}.
		The value \eqn{(1-tau'_n) \in (0,1)}{(1-tau'_n) in (0,1)} is meant to be a small tail probability such that \eqn{(1-\tau'_n)=1/n} or \eqn{(1-\tau'_n) < 1/n}. It is also assumed that \eqn{n(1-\tau'_n) \to C}{n(1-\tau'_n) -> C} as \eqn{n \to \infty}{n -> \infty}, where \eqn{C} is a positive finite constant. Typically, \eqn{C \in (0,1)}{C in (0,1)} so it is expected that there are no observations in a data sample that are greater than the expectile at the extreme level \eqn{\tau_n'}.
		\item When \code{method='LAWS'}, then the \eqn{\tau'_n}-\emph{th} expectile is estimated using the LAWS based estimator. When \code{method='QB'}, the expectile is instead estimated using the QB esimtator. The definition of both estimators depend on the estimation of the tail index \eqn{\gamma}. When \code{tailest='Hill'} then \eqn{\gamma} is estimated using the Hill estimator (see \link{HTailIndex}). When \code{tailest='ExpBased'}, then \eqn{\gamma} is estimated using the expectile based estimator (see \link{EBTailIndex}). See Section 3.2 in Padoan and Stupfler (2020) for details.
		\item If \code{var=TRUE} then an esitmate of the asymptotic variance of the \eqn{tau'_n}-\emph{th} expectile is computed. Notice that the estimation of the asymptotic variance \bold{is only available} when \eqn{\gamma} is estimated using the Hill estimator (see \link{HTailIndex}). With independent observations the asymptotic variance is estimated by \eqn{\hat{\gamma}^2}, see the remark below Theorem 3.5 in Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Ind"}.  With serial dependent observations the asymptotic variance is estimated by the formula in Throrem 3.5 of Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Dep"}. See Section 3.2 in Padoan and Stupfler (2020) for details. In this latter case the computation of the serial dependence is based on the "big blocks seperated by small blocks" techinque which is a standard tools in time series, see e.g. Leadbetter et al. (1986).
		The size of the big and small blocks are specified by the parameters \code{bigBlock} and \code{smallBlock}, respectively.
		\item If \code{bias=TRUE} then \eqn{\gamma} is estimated using formula (4.2) of Haan et al. (2016). This is used by the LAWS and QB estimators. Furthermore, the \eqn{\tau'_n}--\emph{th} quantile is estimated using the formula in page 330 of de Haan et al. (2016). This provides a bias corrected version of the Weissman estimator. This is used by the QB estimator.
		However, in this case the asymptotic variance is not estimated using the formula in Haan et al. (2016) Theorem 4.2. Instead, for simplicity the asymptotic variance is estimated by the formula in Corollary 3.8, with serial dependent observations, and \eqn{\hat{\gamma}^2} with independent observation (see e.g. de Drees 2000, for the details).
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, when \code{tau=NULL} and \code{method='LAWS'}, then \eqn{\tau_n=1-k_n/n} is the intermediate level of the expectile to be stimated. The latter is also used to estimate the tail index when \code{tailest='ExpBased'}. Instead, if \code{tailest='Hill'}, then \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics used in the definition of the Hill estimator. Differently, When \code{tau=NULL} and \code{method='QB'}, then \eqn{\tau_n=1-k_n/n} is the intermediate level of the quantile to be stimated and of the expectile to be stimated when \code{tailest='ExpBased'}. Instead, when \code{tailest='Hill'} it is the numer of \code{k}\eqn{+1} larger order statistics used in the definition of the Hill estimator.
        \item If quantile's extreme level is provided by \code{alpha_n}, then expectile's extreme level \eqn{tau'_n(\alpha_n)} is replaced by \eqn{tau'_n(\alpha_n)} which is esitmated using the method described in Section 6 of Padoan and Stupfler (2020). See \link{estExtLevel} for details.
		\item Given a small value \eqn{\alpha\in (0,1)} then an estimate of an asymptotic confidence interval for \eqn{tau'_n}-\emph{th} expectile, with approximate nominal confidence level \eqn{(1-\alpha)100\%}, is computed. The confidence intervals are computed exploiting formula (10) and (11) in Padoan and Stupfler (2020) and (46) in Drees (2003). See Section 5 in Padoan and Stupfler (2020) for details. When \code{biast=TRUE} confidence intervals are computed in the same way but after correcting the tail index estimate by an estimate of the bias term, see formula (4.2) in de Haan et al. (2016) for details.
	}
}

\value{
  A list with elements:
    \itemize{
	  \item \code{EExpcHat}: an estimate of the \eqn{\tau'_n}-\emph{th} expecile;
	  \item \code{VarExtHat}: an estimate of the asymptotic variance of the expectile estimator;
	  \item \code{CIExpct}: an estimate of the approximate \eqn{(1-\alpha)100\%} confidence interval for \eqn{\tau'_n}-\emph{th} expecile.
	}
}

\references{
Padoan A.S. and Stupfler, G. (2020). Extreme expectile estimation for heavy-tailed time series. \emph{arXiv e-prints} arXiv:2004.04078, \url{https://arxiv.org/abs/2004.04078}.

Daouia, A., Girard, S. and Stupfler, G. (2018). Estimation of tail risk based on extreme expectiles. \emph{Journal of the Royal Statistical Society: Series B}, \bold{80}, 263-292.

de Haan, L., Mercadier, C. and Zhou, C. (2016). Adapting extreme value statistics
tonancial time series: dealing with bias and serial dependence. \emph{Finance and Stochastics},
\bold{20}, 321-354.

Drees, H. (2003). Extreme quantile estimation for dependent data, with applications to finance.
\emph{Bernoulli}, \bold{9}, 617-657.

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
	\link{HTailIndex},  \link{EBTailIndex}, \link{estExpectiles}, \link{extQuantile}
}

\examples{
# Extreme expectile estimation at the extreme level tau1 obtained with
# 1-dimensional data simulated from an AR(1) with univariate
# Student-t distributed innovations

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
tau <- 0.95
# Extreme level (or tail probability 1-tau1 of unobserved expectile)
tau1 <- 0.9995

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rtimeseries(ndata, tsDist, tsType, par)

# Extreme expectile estimation
expectHat1 <- predExpectiles(data, tau, tau1, var=TRUE, bigBlock=bigBlock,
	                         smallBlock=smallBlock)
expectHat1$EExpcHat
expectHat1$CIExpct
# Extreme expectile estimation with bias correction
tau <- 0.80
expectHat2 <- predExpectiles(data, tau, tau1, "QB", var=TRUE, bias=TRUE, bigBlock=bigBlock,
							 smallBlock=smallBlock)
expectHat2$EExpcHat
expectHat2$CIExpct
}
