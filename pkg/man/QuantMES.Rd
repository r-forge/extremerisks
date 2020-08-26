\name{QuantMES}
\alias{QuantMES}

\title{Marginal Expected Shortfall Quantile Based Estimation}
\description{Computes a point and interval estimate of the Marginal Expected Shortfall (MES) using a quantile based approach.}
\usage{
QuantMES(data, tau, tau1, var=FALSE, varType="asym-Dep", bias=FALSE, bigBlock=NULL,
         smallBlock=NULL, k=NULL, alpha=0.05)
}

\arguments{
	\item{data}{A vector of \eqn{(1 \times n)}{(1 x n)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}.}
	\item{tau1}{A real in \eqn{(0,1)} specifying the extreme level \eqn{\tau'_n}. See \bold{Details}.}
	\item{var}{If \code{var=TRUE} then an estimate of the asymptotic variance of the MES estimator is computed.}
	\item{varType}{A string specifying the type of asymptotic variance to compute. By default \code{varType="asym-Dep"} specifies the variance estimator for serial dependent observations. See \bold{Details}.}
	\item{bias}{A logical value. By default \code{bias=FALSE} specifies that no bias correction is computed. See \bold{Details}.}
	\item{bigBlock}{An interger specifying the size of the big-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{smallBlock}{An interger specifying the size of the small-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence interval for the expecile at the intermedite level.}
}

\details{
	For a dataset \code{data} of sample size \eqn{n}, an estimate of the \eqn{\tau'_n}-\emph{th} MES is computed. The estimation of the MES at the extreme level \code{tau1} (\eqn{\tau'_n}) is indeed meant to be a prediction. Estimates are obtained through the quantile based estimator defined in page 12 of Padoan and Stupfler (2020). Such an estimator depends on the estimation of the tail index \eqn{\gamma}. Here, \eqn{\gamma} is estimated using the Hill estimation (see \link{HTailIndex} for details).
	The observations can be either independent or temporal dependent. See Section 4 in Padoan and Stupfler (2020) for details.
	\itemize{
		\item The so-called intermediate level \code{tau} or \eqn{\tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. See \link{predExpectiles} for details.
		\item The so-called extreme level \code{tau1} or \eqn{\tau'_n} is a sequence of positive reals such that \eqn{\tau'_n \to 1}{\tau'_n -> 1} as \eqn{n \to \infty}{n -> \infty}. See \link{predExpectiles} for details.
		\item If \code{var=TRUE} then an esitmate of the asymptotic variance of the \eqn{tau'_n}-\emph{th} MES is computed. Notice that the estimation of the asymptotic variance \bold{is only available} when \eqn{\gamma} is estimated using the Hill estimator (see \link{HTailIndex}). With independent observations the asymptotic variance is estimated by \eqn{\hat{\gamma}^2}, see Corollary 4.3 in Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Ind"}.  With serial dependent observations the asymptotic variance is estimated by the formula in Corollary 4.2 of Padoan and Stupfler (2020). This is achieved through \code{varType="asym-Dep"}. See Section 4 and 5 in Padoan and Stupfler (2020) for details. In this latter case the computation of the serial dependence is based on the "big blocks seperated by small blocks" techinque which is a standard tools in time series, see e.g. Leadbetter et al. (1986).
		The size of the big and small blocks are specified by the parameters \code{bigBlock} and \code{smallBlock}, respectively.
		\item If \code{bias=TRUE} then \eqn{\gamma} is estimated using formula (4.2) of Haan et al. (2016). This is used by the LAWS and QB estimators. Furthermore, the \eqn{\tau'_n}--\emph{th} quantile is estimated using the formula in page 330 of de Haan et al. (2016). This provides a bias corrected version of the Weissman estimator. This is used by the QB estimator.
		However, in this case the asymptotic variance is not estimated using the formula in Haan et al. (2016) Theorem 4.2. Instead, for simplicity the asymptotic variance is estimated by the formula in Corollary 3.8, with serial dependent observations, and \eqn{\hat{\gamma}^2} with independent observation (see e.g. de Drees 2000, for the details).
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics used in the definition of the Hill estimator (see \link{HTailIndex} for details).
        \item If the quantile's extreme level is provided by \code{alpha_n}, then expectile's extreme level \eqn{tau'_n} is replaced by \eqn{tau'_n(\alpha_n)} which is estimated by the method described in Section 6 of Padoan and Stupfler (2020). See \link{estExtLevel} for details.
		\item Given a small value \eqn{\alpha\in (0,1)} then an estimate of an asymptotic confidence interval for \eqn{tau'_n}-\emph{th} expectile, with approximate nominal confidence level \eqn{(1-\alpha)100\%}, is computed. The confidence intervals are computed exploiting formula in Corollary 4.2, Theorem 6.2 of Padoan and Stupfler (2020) and (46) in Drees (2003). See Sections 4-6 in Padoan and Stupfler (2020) for details. When \code{biast=TRUE} confidence intervals are computed in the same way but after correcting the tail index estimate by an estimate of the bias term, see formula (4.2) in de Haan et al. (2016) for details.
	}
}

\value{
  A list with elements:
    \itemize{
	  \item \code{HatQMES}: an estimate of the \eqn{\tau'_n}-\emph{th} quantile based MES;
	  \item \code{VarHatQMES}: an estimate of the asymptotic variance of the quantile based MES estimator;
	  \item \code{CIHatQMES}: an estimate of the approximate \eqn{(1-\alpha)100\%} confidence interval for \eqn{\tau'_n}-\emph{th} MES.
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
	\link{ExpectMES}, \link{HTailIndex},  \link{predExpectiles}, \link{extQuantile}
}

\examples{
# Marginl Expected Shortfall quantile based estimation at the extreme level
# obtained with 2-dimensional data simulated from an AR(1) with bivariate
# Student-t distributed innovations


tsDist <- "AStudentT"
tsType <- "AR"
tsCopula <- "studentT"

# parameter setting
corr <- 0.8
dep <- 0.8
df <- 3
par <- list(corr=corr, dep=dep, df=df)

# Big- small-blocks setting
bigBlock <- 65
smallBlock <- 15

# quantile's extreme level
tau1 <- 0.9995

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rbtimeseries(ndata, tsDist, tsType, tsCopula, par)


# Extreme MES expectile based estimation
MESHat <- QuantMES(data, NULL, tau1, var=TRUE, k=150, bigBlock=bigBlock,
                   smallBlock=smallBlock)
MESHat

}
