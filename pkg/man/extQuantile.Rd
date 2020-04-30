\name{extQuantile}
\alias{extQuantile}

\title{Value-at-Risk (VaR) or Extreme Quantile (EQ) Estimation}
\description{Computes a point and interval estimate of the VaR based on the Weissman estimator.}
\usage{
extQuantile(data, tau, tau1, var=FALSE, varType="asym-Dep", bias=FALSE, bigBlock=NULL,
            smallBlock=NULL, k=NULL, alpha=0.05)
}

\arguments{
	\item{data}{A vector of \eqn{(1 \times n)}{(1 x n)} observations.}
	\item{tau}{A real in \eqn{(0,1)} specifying the intermediate level \eqn{\tau_n}. See \bold{Details}.}
	\item{tau1}{A real in \eqn{(0,1)} specifying the extreme level \eqn{\tau'_n}. See \bold{Details}.}
	\item{var}{If \code{var=TRUE} then an estimate of the asymptotic variance of the VaR estimator is computed.}
	\item{varType}{A string specifying the type of asymptotic variance to compute. By default \code{varType="asym-Dep"} specifies the variance estimator for serial dependent observations. See \bold{Details}.}
	\item{bias}{A logical value. By default \code{biast=FALSE} specifies that no bias correction is computed. See \bold{Details}.}
	\item{bigBlock}{An interger specifying the size of the big-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{smallBlock}{An interger specifying the size of the small-block used to estimaste the asymptotic variance. See \bold{Details}.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
	\item{alpha}{A real in \eqn{(0,1)} specifying the confidence level \eqn{(1-\alpha)100\%} of the approximate confidence interval for the VaR.}
}

\details{
	For a dataset \code{data} of sample size \eqn{n}, the VaR or EQ, correspoding to the extreme level \code{tau1}, is computed by applying the Weissman estimator. The definition of the Weissman estimator depends on the estimation of the tail index \eqn{\gamma}. Here, \eqn{\gamma} is estimated using the Hill estimation (see \link{HTailIndex}). The observations can be either independent or temporal dependent (see e.g. de Haan and Ferreira 2006; Drees 2003; de Haan et al. 2016 for details).
	\itemize{
		\item The so-called intermediate level \code{tau} or \eqn{\tau_n} is a sequence of positive reals such that \eqn{\tau_n \to 1}{\tau_n -> 1} as \eqn{n \to \infty}{n -> \infty}. Practically, \eqn{(1-\tau_n)\in (0,1)}{(1-\tau_n) in (0,1)} is a small proportion of observations in the observed data sample that exceed the \eqn{tau_n}-\emph{th} empirical quantile. Such proportion of observations is used to estimate the \eqn{tau_n}-\emph{th} quantile and \eqn{\gamma}.
		\item The so-called extreme level \code{tau1} or \eqn{\tau'_n} is a sequence of positive reals such that \eqn{\tau'_n \to 1}{\tau'_n -> 1} as \eqn{n \to \infty}{n -> \infty}.
		The value \eqn{(1-tau'_n) \in (0,1)}{(1-\tau'_n) in (0,1)} is meant to be a small tail probability such that \eqn{(1-\tau'_n)=1/n} or \eqn{(1-\tau'_n) < 1/n}. It is also assumed that \eqn{n(1-\tau'_n) \to C}{n(1-tau'_n) -> C} as \eqn{n \to \infty}{n -> \infty}, where \eqn{C} is a positive finite constant. The value \eqn{C} is the expected number of exceedances of the \eqn{\tau'_n}-\emph{th} quantile. Typically, \eqn{C \in (0,1)}{C in (0,1)} which means that it is expected that there are no observations in a data sample exceeding the quantile of level \eqn{(1-\tau_n')}.
		\item If \code{var=TRUE} then an esitmate of the asymptotic variance of the \eqn{tau'_n}-\emph{th} quantile is computed. With independent observations the asymptotic variance is estimated by the formula \eqn{\hat{\gamma}^2} (see e.g. de Drees 2000, 2003, for details). This is achieved through \code{varType="asym-Ind"}. With serial dependent data the asymptotic variance is estimated by the formula in 1288 in Drees (2000). This is achieved through  \code{varType="asym-Dep"}. In this latter case the computation of the serial dependence is based on the "big blocks seperated by small blocks" techinque which is a standard tools in time series, see e.g. Leadbetter et al. (1986). The size of the big and small blocks are specified by the parameters \code{bigBlock} and \code{smallBlock}, respectively. With serial dependent data the asymptotic variance can also be estimated by formula (32) of Drees (2003). This is achieved through \code{varType="asym-Alt-Dep"}.
		\item If \code{bias=TRUE} then an estimate of the \eqn{\tau'_n}--\emph{th} quantile is computed using the formula in page 330 of de Haan et al. (2016), which provides a bias corrected version of the Weissman estimator. However, in this case the asymptotic variance is not estimated using the formula in Haan et al. (2016) Theorem 4.2. Instead, for simplicity standard formula in Drees (2000) page 1288 is used.
		\item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, the value \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics to be used to estimate the \eqn{\tau_n}-\emph{th} empirical quantile and \eqn{\gamma}. The intermediate level \eqn{\tau_n} can be seen defined as \eqn{\tau_n=1-k_n/n}.
        \item Given a small value \eqn{\alpha\in (0,1)} then an estimate of an asymptotic confidence interval for \eqn{tau'_n}-\emph{th} quantile, with approximate nominal confidence level \eqn{(1-\alpha)100\%}, is computed. The confidence intervals are computed exploiting the formulas (33) and (46) of Drees (2003). When \code{biast=TRUE} confidence intervals are computed in the same way but after correcting the tail index estimate by an estimate of the bias term, see formula (4.2) in de Haan et al. (2016) for details. Furthermore, in this case with serial dependent data the asymptotic variance is estimated using the formula in Drees (2000) page 1288.
	}
}

\value{
	A list with elements:
	\itemize{
		\item \code{ExtQHat}: an estimate of the VaR or \eqn{\tau'_n}-\emph{th} quantile;
		\item \code{VarExQHat}: an estimate of the asymptotic variance of the VaR estimator;
		\item \code{CIExtQ}: an estimate of the approximate \eqn{(1-\alpha)100\%} confidence interval for the VaR.
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

  Drees, H. (2003). Extreme quantile estimation for dependent data, with applications to finance.
  \emph{Bernoulli}, \bold{9}, 617-657.

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
	\link{HTailIndex}, \link{EBTailIndex}, \link{estExpectiles}
}

\examples{
# Extreme quantile estimation at the level tau1 obtained with 1-dimensional data
# simulated from an AR(1) with univariate Student-t distributed innovations

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
tau <- 0.97
# Extreme level (or tail probability 1-tau1 of unobserved quantile)
tau1 <- 0.9995

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rtimeseries(ndata, tsDist, tsType, par)

# VaR (extreme quantile) estimation
extQHat1 <- extQuantile(data, tau, tau1, TRUE, bigBlock=bigBlock, smallBlock=smallBlock)
extQHat1$ExtQHat
extQHat1$CIExtQ

# VaR (extreme quantile) estimation with bias correction
extQHat2 <- extQuantile(data, tau, tau1, TRUE, bias=TRUE, bigBlock=bigBlock, smallBlock=smallBlock)
extQHat2$ExtQHat
extQHat2$CIExtQ
}
