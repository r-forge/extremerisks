\name{rmdata}
\alias{rmdata}

\title{Simulation of \eqn{d}-Dimensional Temporally Independent Observations}
\description{Simulates samples of independent \eqn{d}-dimensional observations from parametric families of joint distributions with a given copula and equal marginal distributions.}
\usage{
rmdata (ndata, dist="studentT", copula="studentT", par)
}

\arguments{
	\item{ndata}{A positive interger specifying the number of observations to simulate.}
	\item{dist}{A string specifying the parametric family of equal marginal distributions. By default \code{dist="studentT"} specifies a
    Student-\emph{t} family of distributions. See \bold{Details}.}
	\item{copula}{A string specifying the type copula to be used. By default \code{copula="studentT"} specifies the Student-\emph{t} copula. See \bold{Details}.}
	\item{par}{A list of \eqn{p} parameters to be specified for the multivariate parametric family of distributions. See \bold{Details}.}
}

\details{
	For a joint multivariate distribution with a given parametric copula class (\code{copula}) and a given parametric family of equal marginal distributions (\code{dist}), a sample of size \code{ndata} is simulated.
	\itemize{
		\item The available copula classes are: Student-\emph{t} (\code{copula="studentT"}) with \eqn{\nu>0} degrees of freedom (\code{df}) and scale parameters \eqn{\rho_{i,j}\in (-1,1)} for \eqn{i \neq j=1,\ldots,d}{i != j=1,...,d} (\code{sigma}), Gaussian (\code{copula="Gaussian"}) with correlation parameters \eqn{\rho_{i,j}\in (-1,1)} for \eqn{i \neq j=1,\ldots,d}{i != j=1,...,d} (\code{sigma}), Clayton (\code{copula="Clayton"}) with dependence parameter \eqn{\theta>0} (\code{dep}), Gumbel (\code{copula="Gumbel"}) with dependence parameter \eqn{\theta\geq 1} (\code{dep}) and Frank (\code{copula="Frank"}) with dependence parameter \eqn{\theta>0} (\code{dep}).
        \item The available families of marginal distributions are:
        \itemize{
        \item Student-\emph{t} (\code{dist="studentT"}) with \eqn{\nu>0} degrees of freedom (\code{df});
		\item Asymmetric Student-\emph{t} (\code{dist="AStudentT"}) with \eqn{\nu>0} degrees of freedom (\code{df}). In this case all the observations are only positive;
		\item Frechet (\code{dist="Frechet"}) with scale \eqn{\sigma>0} (\code{scale}) and shape \eqn{\alpha>0} (\code{shape}) parameters.
		\item Frechet (\code{dist="double-Frechet"}) with scale \eqn{\sigma>0} (\code{scale}) and shape \eqn{\alpha>0} (\code{shape}) parameters. In this case positive and negative observations are allowed;
		\item symmetric Pareto (\code{dist="double-Pareto"}) with scale \eqn{\sigma>0} (\code{scale}) and shape \eqn{\alpha>0} (\code{shape}) parameters. In this case positive and negative observations are allowed.
        }
		\item The available classes of multivariate joint distributions are:
        \itemize{
        \item studentT-studentT (\code{dist="studentT"} and \code{copula="studentT"}) with parameters \code{par <- list(df, sigma)};
		\item studentT (\code{dist="studentT"} and \code{copula="None"} with parameters \code{par <- list(df, dim)}. In this case the \code{d} variables are regarded as independent;
		\item studentT-AstudentT (\code{dist="AstudentT"} and \code{copula="studentT"}) with parameters \code{par <- list(df, sigma, shape)};
		\item Gaussian-studentT (\code{dist="studentT"} and \code{copula="Gaussian"}) with parameters \code{par <- list(df, sigma)};
		\item Gaussian-AstudentT (\code{dist="AstudentT"} and \code{copula="Gaussian"}) with parameters \code{par <- list(df, sigma, shape)};
		\item Frechet (\code{dist="Frechet"} and \code{copula="None"}) with parameters \code{par <- list(shape, dim)}. In this case the \code{d} variables are regarded as independent;
		\item Clayton-Frechet (\code{dist="Frechet"} and \code{copula="Clayton"}) with parameters \code{par <- list(dep, dim, scale, shape)};
		\item Gumbel-Frechet (\code{dist="Frechet"} and \code{copula="Gumbel"}) with parameters \code{par <- list(dep, dim, scale, shape)};
		\item Frank-Frechet (\code{dist="Frechet"} and \code{copula="Frank"}) with parameters \code{par <- list(dep, dim, scale, shape)};
		\item Clayton-double-Frechet (\code{dist="double-Frechet"} and \code{copula="Clayton"}) with parameters \code{par <- list(dep, dim, scale, shape)};
		\item Gumbel-double-Frechet (\code{dist="double-Frechet"} and \code{copula="Gumbel"}) with parameters \code{par <- list(dep, dim, scale, shape)};
		\item Frank-double-Frechet (\code{dist="double-Frechet"} and \code{copula="Frank"}) with parameters \code{par <- list(dep, dim, scale, shape)};
		\item Clayton-double-Pareto (\code{dist="double-Pareto"} and \code{copula="Clayton"}) with parameters \code{par <- list(dep, dim, scale, shape)};
		\item Gumbel-double-Pareto (\code{dist="double-Pareto"} and \code{copula="Gumbel"}) with parameters \code{par <- list(dep, dim, scale, shape)};
		\item Frank-double-Pareto (\code{dist="double-Pareto"} and \code{copula="Frank"}) with parameters \code{par <- list(dep, dim, scale, shape)}.
        }
		Note that above \code{dim} indicates the number of \code{d} marginal variables.
	}
}

\value{
A matrix of \eqn{(n \times d)}{(n x d)} observations simulated from a specified multivariate parametric joint distribution.
}


\references{
Joe, H. (2014). Dependence Modeling with Copulas. Chapman & Hall/CRC Press, Boca
Raton, USA.

Padoan A.S. and Stupfler, G. (2020). Joint inference on extreme expectiles for multivariate
heavy-tailed distributions. \emph{arXiv e-prints} arXiv:2007.08944, \url{https://arxiv.org/abs/2007.08944}.
}

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://mypage.unibocconi.it/simonepadoan/};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{rtimeseries}, \link{rbtimeseries}
}

\examples{
library(plot3D)
library(copula)
library(evd)

# Data simulation from a 3-dimensional random vector a with multivariate distribution
# given by a Gumbel copula and three equal Frechet marginal distributions

# distributional setting
copula <- "Gumbel"
dist <- "Frechet"

# parameter setting
dep <- 3
dim <- 3
scale <- rep(1, dim)
shape <- rep(3, dim)
par <- list(dep=dep, scale=scale, shape=shape, dim=dim)

# sample size
ndata <- 1000

# Simulates a sample from a multivariate distribution with equal Frechet
# marginal distributions and a Gumbel copula
data <- rmdata(ndata, dist, copula, par)
scatter3D(data[,1], data[,2], data[,3])


# Data simulation from a 3-dimensional random vector a with multivariate distribution
# given by a Gaussian copula and three equal Student-t marginal distributions

# distributional setting
dist <- "studentT"
copula <- "Gaussian"

# parameter setting
rho <- c(0.9, 0.8, 0.7)
sigma <- c(1, 1, 1)
Sigma <- sigma^2 * diag(dim)
Sigma[lower.tri(Sigma)] <- rho
Sigma <- t(Sigma)
Sigma[lower.tri(Sigma)] <- rho
df <- 3
par <- list(sigma=Sigma, df=df)

# sample size
ndata <- 1000

# Simulates a sample from a multivariate distribution with equal Student-t
# marginal distributions and a Gaussian copula
data <- rmdata(ndata, dist, copula, par)
scatter3D(data[,1], data[,2], data[,3])
}
