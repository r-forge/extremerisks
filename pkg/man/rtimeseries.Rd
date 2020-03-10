\name{rtimeseries}
\alias{rtimeseries}

\title{Simulation of Temporally Dependent Observations}
\description{Simulates samples from parametric families of time series models.}
\usage{
rtimeseries(ndata, dist="studentT", type="AR", par, burnin=1e+03)

}

\arguments{
	\item{ndata}{A positive interger specifying the number of observations to simulate.}
	\item{dist}{A string specifying the parametric family of the innovations distribution. By default \code{dist="studentT"} specifies a
    Student-\emph{t} family of distributions. See \bold{Details}.}
	\item{type}{A string specifying the type of time series. By default \code{type="AR"} specifies a linear Auto-Regressive time series. See \bold{Details}.}
	\item{par}{A vector of \eqn{(1 \times p)}{(1 x p)} parameters of the time series parametric family. See \bold{Details}.}
	\item{burnin}{A positive interger specifying the number of initial observations to discard from the simulated sample.}

}

\details{
	For a time series class (\code{type}) with a parametric family (\code{dist}) for the innovations, a sample of size \code{ndata} is simulated. See for example Brockwell and Davis (2016).
	\itemize{
		\item The available types of time series models are: Auto-Regressive (\code{type="AR"}), Auto-Regressive and Moving-Average (\code{type="ARMA"}), Generalized-Autoregressive-Conditional-Heteroskedasticity (\code{type="GARCH"}) and Auto-Regressive and Moving-Maxima (\code{type="ARMAX"}).
		\item With AR(1) and ARMA(1,1) times series the available families of distributions for the innovations are:
        \itemize{
        \item Student-\emph{t} (\code{dist="studentT"}) with parameters \eqn{\phi} (autoregressive coefficient), \eqn{\nu} (degress of freedom) specified by \code{par=c(corr, df)};
        \item symmetric Frechet (\code{dist="double-Frechet"}) with parameters \eqn{\phi} (autoregressive coefficient), \eqn{\sigma} (scale),   \eqn{\alpha} (shape), \eqn{\theta} (movingaverage coefficient), specified by \code{par=c(corr, scale, shape, smooth)};
        \item symmetric Pareto (\code{dist="double-Pareto"}) with parameters \eqn{\phi} (autoregressive coefficient), \eqn{\sigma} (scale),   \eqn{\alpha} (shape), \eqn{\theta} (movingaverage coefficient), specified by \code{par=c(corr, scale, shape, smooth)}.
        }
        With ARCH(1)/GARCH(1,1) time series the Gaussian family of distributions is available for the innovations (\code{dist="Gaussian"}) with parameters, \eqn{\alpha_0}, \eqn{\alpha_1}, \eqn{\beta} specified by \code{par=c(alpha0, alpha1, beta)}. Finally, with ARMAX(1) times series the Frechet families of distributions is available for the innovations (\code{dist="Frechet"}) with parameters, \eqn{\phi} (autoregressive coefficient), \eqn{\sigma} (scale), \eqn{\alpha} (shape) specified by \code{par=c(corr, scale, shape)}.
	}
}

\value{
  A vector of \eqn{(1 \times n)}{(1 x n)} observations simulated by a specified time series model.

}

\references{
Brockwell, Peter J., and Richard A. Davis. (2016). Introduction to time series and forecasting. \emph{Springer}.

}

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://faculty.unibocconi.it/simonepadoan};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{expectiles}
}

\examples{
# Data simulation from AR(1) with Student-t innovations
tsDist <- "studentT"
tsType <- "AR"

# parameter setting
corr <- 0.8
df <- 3
par <- c(corr, df)

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rtimeseries(ndata, tsDist, tsType, par)

# Extreme expectile estimation
plot(data, type="l")
acf(data)

}
