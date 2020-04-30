\name{MomTailIndex}
\alias{MomTailIndex}

\title{Moment based Tail Index Estimation}
\description{Computes a point estimate of the tail index based on the Moment Based (MB) estimator.}
\usage{
MomTailIndex(data, k)
}

\arguments{
	\item{data}{A vector of \eqn{(1 \times n)}{(1 x n)} observations.}
	\item{k}{An integer specifying the value of the intermediate sequence \eqn{k_n}. See \bold{Details}.}
}

\details{
	For a dataset \code{data} of sample size \eqn{n}, the tail index \eqn{\gamma} of its (marginal) distribution is computed by applying the MB estimator. The observations can be either independent or temporal dependent. For details see de Haan and Ferreira (2006).
	\itemize{
        \item \code{k} or \eqn{k_n} is the value of the so-called intermediate sequence \eqn{k_n}, \eqn{n=1,2,\ldots}{n=1,2,...}. Its represents a sequence of positive integers such that \eqn{k_n \to \infty}{k_n -> \infty} and \eqn{k_n/n \to 0}{k_n/n -> 0} as \eqn{n \to \infty}{n -> \infty}. Practically, the value \eqn{k_n} specifies the number of \code{k}\eqn{+1} larger order statistics to be used to estimate \eqn{\gamma}.
	}
}

\value{
An estimate of the tail index \eqn{\gamma}.
}

\references{
de Haan, L. and Ferreira, A. (2006). Extreme Value Theory: An Introduction. \emph{Springer}-\emph{Verlag}, New York.
}

\author{
	Simone Padoan, \email{simone.padoan@unibocconi.it},
	\url{http://mypage.unibocconi.it/simonepadoan/};
	Gilles Stupfler, \email{gilles.stupfler@ensai.fr},
	\url{http://ensai.fr/en/equipe/stupfler-gilles/}
}

\seealso{
	\link{HTailIndex}, \link{MLTailIndex}, \link{EBTailIndex}
}

\examples{
# Tail index estimation based on the Moment estimator obtained with
# 1-dimensional data simulated from an AR(1) with univariate Student-t
# distributed innovations

tsDist <- "studentT"
tsType <- "AR"

# parameter setting
corr <- 0.8
df <- 3
par <- c(corr, df)

# Big- small-blocks setting
bigBlock <- 65
smallblock <- 15

# Number of larger order statistics
k <- 150

# sample size
ndata <- 2500

# Simulates a sample from an AR(1) model with Student-t innovations
data <- rtimeseries(ndata, tsDist, tsType, par)

# tail index estimation
gammaHat <- MomTailIndex(data, k)
gammaHat
}
