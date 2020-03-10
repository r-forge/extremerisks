\name{expectiles}
\alias{expectiles}

\title{Expectile Computation}
\description{Computes the true expectile for some families of parametric models.}
\usage{
expectiles(par, tau, tsDist="gPareto", tsType="IID", trueMethod="true",
           estMethod="LAWS", nrep=1e+05, ndata=1e+06, burnin=1e+03)
}

\arguments{
	\item{par}{A vector of \eqn{(1 \times p)}{(1 x p)} parameters of the time series parametric family. See \bold{Details}.}
	\item{tau}{A real in \eqn{(0,1)} specifying the level \eqn{\tau} of the expectile to be computed. See \bold{Details}.}
	\item{tsDist}{A string specifying the parametric family of the innovations distribution. By default \code{tsDist="gPareto"} specifies a
    Pareto family of distributions. See \bold{Details}.}
    \item{tsType}{A string specifying the type of time series. By default \code{tsType="IID"} specifies a sequence of independent and indentically distributed random variables. See \bold{Details}.}
	\item{trueMethod}{A string specifying the method used to computed the expecile. By default \code{trueMethod="true"} specifies that the true analytical expression to computed the expectile is used. See \bold{Details}.}
	\item{estMethod}{A string specifying the method used to estimate the expecile. By default \code{est="LAWS"} specifies the use of the direct LAWS estimator. See \bold{Details}.}
	\item{nrep}{A positive interger specifying the number of simulations to use for computing an approximation of the expectile. See \bold{Details}.}
	\item{ndata}{A positive interger specifying the number of observations to genreated for each simulation. See \bold{Details}.}
	\item{burnin}{A positive interger specifying the number of initial observations to discard from the simulated sample.}

}

\details{
	For a parametric family of time series models or a parametric family of distributions (for the case of independent observations) the \eqn{\tau}-\emph{th} expectile (or expectile of level \code{tau}) is computed.
	\itemize{
		\item There are two methods to compute the \eqn{\tau}-\emph{th} expectile. For the Generalised Pareto and Student-\emph{t} parametric families of distributions, the analytical epxression of the expectile is available. This is used to compute the \eqn{\tau}-\emph{th} expectile if the parameter \code{trueMethod="true"} is specified. For most of parametric family of distributions or parametric families of time series models the analytical epxression of the expectile is not available. In this case an approximate value of the \eqn{\tau}-\emph{th} expectile is computed via a Monte Carlo method if the parameter \code{trueMethod=="approx"} is specified. In particular, \code{ndata} observations from a family of time series models (e.g. \code{tsType="AR"} and \code{tsDist="studentT"}) or a sequence of independent and indentically distributed random variables with common family of distributions (e.g. \code{tsType="IID"} and \code{tsDist="gPareto"}) are simulated \code{nrep} times. For each simulation the \eqn{\tau}-\emph{th} expectile is estimate by the estimation method specified by \code{estMethod}. The mean of such estimate provides an approximate value of the \eqn{\tau}-\emph{th} expectile. The available estimator to esitmate the expecile are the direct LAWS (\code{estMethod="LAWS"}) and the indirect QB (\code{estMethod="QB"}), see \link{estExpectiles} for details. The available families of distributions are: Generalised Pareto (\code{tsDist="gPareto"}), Student-\emph{t} (\code{tsDist="studentT"}) and Frechet (\code{tsDist="Frechet"}). The available classes of time series with parametric innovations families of distributions are specified in \link{rtimeseries}.
	}
}

\value{
  The \eqn{\tau}-\emph{th} expectile.
}


\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://faculty.unibocconi.it/simonepadoan};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{rtimeseries}
}

\examples{
# tau-th expectile of the Pareto distribution

# parameter value
par <- c(1, 0.3)

# Intermediate level (or sample tail probability 1-tau)
tau <- 0.99

trueExp <- expectiles(par, tau)
trueExp

\donttest{
# tau-th expectile of the AR(1) with Student-t innovations
tsDist <- "studentT"
tsType <- "AR"

# Approximation via Monte Carlo methods
trueMethod <- "approx"

# parameter setting
corr <- 0.8
df <- 3
par <- c(corr, df)

# Intermediate level (or sample tail probability 1-tau)
tau <- 0.99

trueExp <- expectiles(par, tau, tsDist, tsType, trueMethod)
trueExp
}
}
