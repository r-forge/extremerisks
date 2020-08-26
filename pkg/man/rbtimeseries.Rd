\name{rbtimeseries}
\alias{rbtimeseries}

\title{Simulation of Two-Dimensional Temporally Dependent Observations}
\description{Simulates samples from parametric families of bivariate time series models.}
\usage{
rbtimeseries(ndata, dist="studentT", type="AR", copula="Gumbel", par, burnin=1e+03)
}

\arguments{
	\item{ndata}{A positive interger specifying the number of observations to simulate.}
	\item{dist}{A string specifying the parametric family of the innovations distribution. By default \code{dist="studentT"} specifies a
    Student-\emph{t} family of distributions. See \bold{Details}.}
	\item{type}{A string specifying the type of time series. By default \code{type="AR"} specifies a linear Auto-Regressive time series. See \bold{Details}.}
	\item{copula}{A string specifying the type copula to be used. By default \code{copula="Gumbel"} specifies the Gumbel copula. See \bold{Details}.}
	\item{par}{A list of \eqn{p} parameters to be specified for the bivariate time series parametric family. See \bold{Details}.}
	\item{burnin}{A positive interger specifying the number of initial observations to discard from the simulated sample.}
}

\details{
	For a time series class (\code{type}), with a parametric family (\code{dist}) for the innovations, a sample of size \code{ndata} is simulated. See for example Brockwell and Davis (2016).
	\itemize{
		\item The available categories of bivariate time series models are: Auto-Regressive (\code{type="AR"}), Auto-Regressive and Moving-Average (\code{type="ARMA"}), Generalized-Autoregressive-Conditional-Heteroskedasticity (\code{type="GARCH"}) and Auto-Regressive.
        \item With AR(1) times series the available families of distributions for the innovations and the dependence structure (copula) are:
        \itemize{
        \item Student-\emph{t} (\code{dist="studentT"} and \code{copula="studentT"}) with marginal parameters (equal for both distributions): \eqn{\phi\in(-1,1)}{phi in(-1,1)} (autoregressive coefficient), \eqn{\nu>0} (degrees of freedom) and dependence parameter \eqn{dep\in(-1,1)}{dep in (-1,1)}. The parameters are specified as \code{par <- list(corr, df, dep)};
        \item Asymmetric Student-\emph{t} (\code{dist="AStudentT"} and \code{copula="studentT"}) with marginal parameters (equal for both distributions): \eqn{\phi\in(-1,1)}{phi in(-1,1)} (autoregressive coefficient), \eqn{\nu>0} (degrees of freedom) and dependence parameter \eqn{dep\in(-1,1)}{dep in (-1,1)}. The paraters are specified as \code{par <- list(corr, df, dep)}. Note that in this case the tail index of the lower and upper tail of the first marginal are different, see Padoan and Stupfler (2020) for details;
        }
		\item With ARMA(1,1) times series the available families of distributions for the innovations and the dependence structure (copula) are:
        \itemize{
        \item symmetric Pareto (\code{dist="double-Pareto"} and \code{copula="Gumbel"} or \code{copula="Gaussian"}) with marginal parameters (equal for both distributions): \eqn{\phi\in(-1,1)}{phi in(-1,1)} (autoregressive coefficient), \eqn{\sigma>0} (scale), \eqn{\alpha>0} (shape), \eqn{\theta} (movingaverage coefficient), and dependence parameter \eqn{dep} (\eqn{dep>0} if \code{copula="Gumbel"} or \eqn{dep\in(-1,1)}{dep in (-1,1)} if \code{copula="Gaussian"}). The parameters are specified as \code{par <- list(corr, scale, shape, smooth, dep)}.
        \item symmetric Pareto (\code{dist="double-Pareto"} and \code{copula="Gumbel"} or \code{copula="Gaussian"}) with marginal parameters (equal for both distributions): \eqn{\phi\in(-1,1)}{phi in(-1,1)} (autoregressive coefficient), \eqn{\sigma>0} (scale), \eqn{\alpha>0} (shape), \eqn{\theta} (movingaverage coefficient), and dependence parameter \eqn{dep} (\eqn{dep>0} if \code{copula="Gumbel"} or \eqn{dep\in(-1,1)}{dep in (-1,1)} if \code{copula="Gaussian"}). The parameters are specified as \code{par <- list(corr, scale, shape, smooth, dep)}. Note that in this case the tail index of the lower and upper tail of the first marginal are different, see Padoan and Stupfler (2020) for details;
        }
        \item With ARCH(1)/GARCH(1,1) time series the distribution of the innovations are symmetric Gaussian (\code{dist="Gaussian"}) or asymmetric Gaussian \code{dist="AGaussian"}. In both cases the marginal parameters (equal for both distributions) are: \eqn{\alpha_0}, \eqn{\alpha_1}, \eqn{\beta}. In the asymmetric Gaussian case the tail index of the lower and upper tail of the first marginal are different, see Padoan and Stupfler (2020) for details. The available copulas are: Gaussian (\code{copula="Gaussian"}) with dependence parameter \eqn{dep\in(-1,1)}, Student-\emph{t} (\code{copula="studentT"}) with dependence parameters \eqn{dep\in(-1,1)}{dep in (-1,1)} and \eqn{\nu>0} (degrees of freedom), Gumbel (\code{copula="Gumbel"}) with dependence parameter \eqn{dep>0}. The parameters are specified as \code{par <- list(alpha0, alpha1, beta, dep)} or \code{par <- list(alpha0, alpha1, beta, dep, df)}.
	}
}

\value{
  A vector of \eqn{(2 \times n)}{(2 x n)} observations simulated from a specified bivariate time series model.
}

\references{
Brockwell, Peter J., and Richard A. Davis. (2016). Introduction to time series and forecasting. \emph{Springer}.

Padoan A.S. and Stupfler, G. (2020). Extreme expectile estimation for heavy-tailed time series. \emph{arXiv e-prints} arXiv:2004.04078, \url{https://arxiv.org/abs/2004.04078}.
}

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://mypage.unibocconi.it/simonepadoan/};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{rtimeseries}, \link{expectiles}
}

\examples{
# Data simulation from a 2-dimensional AR(1) with bivariate Student-t distributed
# innovations, with one marginal distribution whose lower and upper tail indices
# that are different

tsDist <- "AStudentT"
tsType <- "AR"
tsCopula <- "studentT"

# parameter setting
corr <- 0.8
dep <- 0.8
df <- 3
par <- list(corr=corr, dep=dep, df=df)

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rbtimeseries(ndata, tsDist, tsType, tsCopula, par)

# Extreme expectile estimation
plot(data, pch=21)
plot(data[,1], type="l")
plot(data[,2], type="l")
}
