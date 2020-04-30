#########################################################
### Authors: Simone Padoan and Gilles Stuplfer        ###
### Emails: simone.padoan@unibocconi.it               ###
### gilles.stupfler@ensai.fr                          ###
### Institution: Department of Decision Sciences,     ###
### University Bocconi of Milan, Italy,               ###
### Ecole Nationale de la Statistique et de           ###
### l'Analyse de l'Information, France                ###
### File name: Estimation.r                           ###
### Description:                                      ###
### This file contains a set of procedures            ###
### for simulating i.i.d. data from heavy-tailed      ###
### parametric families of distribution and           ###
### serial dependent data from families of time setie ###
### models with heavy-tailed marginal disribution     ###
### Last change: 2020-04-18                           ###
#########################################################


#########################################################
### START
### Sub-routines (HIDDEN FUNCTIONS)
###
#########################################################

rdoublefrechet <- function(ndata, scale, shape){
  coin <- rbinom(ndata, 1, .5)
  data <- (2*coin-1)*rfrechet(ndata, scale=scale, shape=shape)
  return(data)
}

rdoublepareto <- function(ndata, scale, shape){
  coin <- rbinom(ndata, 1, .5)
  data <- (2*coin-1)*scale*(rgpd(ndata, loc=1, scale=1, shape=1))^(shape)
  return(data)
}

rmdoublepareto <- function(ndata, scale, shape, sigma){
  coin <- rbinom(ndata, 1, .5)
  u <- pnorm(rmvnorm(ndata, sigma=sigma))
  data <- (2*coin-1)*scale*(1-u)^(-1/shape)
  return(data)
}

rmadoublepareto <- function(ndata, dep, scale, shape, copula){
  coin <- rbinom(ndata, 1, .5)
  u <-  rCopula(ndata, copula)
  data <- (2*coin-1)*scale*(1-u)^(-1/shape)
  return(data)
}

#########################################################


#########################################################
### START
### Main-routines (VISIBLE FUNCTIONS)
###
#########################################################

rtimeseries <- function(ndata, dist="studentT", type="AR", par, burnin=1e+03)
{
  # main body
  # Check whether the distribution in input is available
  if(!(dist %in% c("studentT", "double-Frechet", "double-Pareto", "Gaussian", "Frechet"))) stop("insert the correct DISTRIBUTION!")

  # Set output
  res <- NULL
  # compute the design matrix:
  if(type=="AR"){
   if(dist=="studentT"){
     # Stationary auto-regressive time series with Student-t iid innovations
     # Set parameters
     corr <- par[1]
     df <- par[2]
     # Set total number of data
     nsim <- ndata+burnin
     data <- rep(0, nsim)
     z <- sqrt(1-corr^2) * rt(nsim, df)
     for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + z[i]
     data <- data[(burnin+1):nsim]
   }
   if(dist=="double-Frechet"){
     # Stationary auto-regressive time series with double Frechet iid innovations
     # Set parameters
     corr <- par[1]
     scale <- par[2]
     shape <- par[3]
     # Set total number of data
     nsim <- ndata+burnin
     data <- rep(0, nsim)
     z <- sqrt(1-corr^2) * rdoublefrechet(nsim, scale=scale, shape=shape)
     for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + z[i]
     data <- data[(burnin+1):nsim]
   }
   if(dist=="double-Pareto"){
     # Stationary auto-regressive time series with double Pareto iid innovations
     # Set parameters
     corr <- par[1]
     scale <- par[2]
     shape <- par[3]
     # Set total number of data
     nsim <- ndata+burnin
     data <- rep(0, nsim)
     z <- sqrt(1-corr^2) * rdoublepareto(nsim, scale=scale, shape=1/shape)
     for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + z[i]
     data <- data[(burnin+1):nsim]
   }
 }
 # compute the design matrix:
 if(type=="ARMA"){
  if(dist=="studentT"){
    # Stationary auto-regressive time series with Student-t iid innovations
    # Set parameters
    corr <- par[1]
    df <- par[2]
    smooth <- par[3]
    # Set total number of data
    nsim <- ndata+burnin
    data <- rep(0, nsim)
    z <- sqrt(1-corr^2) * rt(nsim, df)
    for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + smooth * z[i] + z[i+1]
    data <- data[(burnin+1):nsim]
  }
  if(dist=="double-Frechet"){
    # Stationary auto-regressive time series with double Frechet iid innovations
    # Set parameters
    corr <- par[1]
    scale <- par[2]
    shape <- par[3]
    smooth <- par[4]
    # Set total number of data
    nsim <- ndata+burnin
    data <- rep(0, nsim)
    z <- sqrt(1-corr^2) * rdoublefrechet(nsim, scale=scale, shape=shape)
    for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + smooth * z[i] + z[i+1]
    data <- data[(burnin+1):nsim]
  }
  if(dist=="double-Pareto"){
    # Stationary auto-regressive time series with double Pareto iid innovations
    # Set parameters
    corr <- par[1]
    scale <- par[2]
    shape <- par[3]
    smooth <- par[4]
    # Set total number of data
    nsim <- ndata+burnin
    data <- rep(0, nsim)
    z <- sqrt(1-corr^2) * rdoublepareto(nsim, scale=scale, shape=1/shape)
    for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + smooth * z[i] + z[i+1]
    data <- data[(burnin+1):nsim]
  }
}
   if(type=="GARCH"){
     if(dist=="Gaussian"){
       # Stationary GARCH time series with Gaussian iid innovations
       # Set parameters
       alpha <- par[1:2]
       beta <- par[3]
       # Set total number of data
       nsim <- ndata+burnin
       data <- rep(0, nsim)
       sigma <- rep(0, nsim)
       z <- rnorm(nsim)
       for(i in 1:(nsim-1)){
         sigma[i+1] <- sqrt(alpha[1] + alpha[2] * data[i]^2 + beta * sigma[i]^2)
         data[i+1] <- sigma[i+1] * z[i]
       }
       data <- data[(burnin+1):nsim]
     }
   }
   if(type=="ARMAX"){
     if(dist=="Frechet"){
       # Set parameters
       corr <- par[1]
       scale <- par[2]
       shape <- par[3]
       # Set total number of data
       nsim <- ndata+burnin
       data <- rep(0, nsim)
       z <- (1-corr)^(1/shape) * rfrechet(nsim, scale=scale, shape=shape)
       for(i in 1:(nsim-1)) data[i+1] <- max((corr)^(1/shape) * data[i],  z[i])
       data <- data[(burnin+1):nsim]
     }
   }
 return(data)
 }

 rbtimeseries <- function(ndata, dist="studentT", type="AR", copula="Gumbel", par, burnin=1e+03)
 {
   # main body
   # Check whether the distribution in input is available
   if(!(dist %in% c("studentT", "AStudentT", "TStudentT", "double-Pareto", "ADouble-Pareto", "Gaussian", "AGaussian"))) stop("insert the correct DISTRIBUTION!")
   # Set output
   res <- NULL
   # compute the design matrix:
   if(type=="IID"){
     if(dist=="studentT"){
       dep <- par$dep
       sigma <- matrix(c(1, dep, dep, 1), ncol=2)
       df <- par$df
       # Stationary time series with symmetric Student-t iid innovations
       data <- rmvt(ndata, sigma, df)
     }
   }
    # compute the design matrix:
    if(type=="AR"){
      if(dist=="studentT" & copula=="studentT"){
        # Stationary auto-regressive time series with symmetric Student-t iid innovations
        # Set parameters
        corr <- par$corr
        df <- par$df
        dep <- par$dep
        sigma <- matrix(c(1, dep, dep, 1), ncol=2)
        # Set total number of data
        nsim <- ndata+burnin
        data <- array(0, c(nsim, 2))
        z <- sqrt(1-corr^2) * rmvt(nsim, sigma, df)
        for(i in 1:(nsim-1)) data[i+1,] <- corr*data[i,] + z[i,]
        data <- data[(burnin+1):nsim,]
      }
      if(dist=="AStudentT" & copula=="studentT"){
        # Stationary auto-regressive time series with asymmetric Student-t iid innovations
        # Set parameters
        corr <- par$corr
        df <- par$df
        dep <- par$dep
        sigma <- matrix(c(1, dep, dep, 1), ncol=2)
        # Set total number of data
        nsim <- ndata+burnin
        data <- array(0, c(nsim, 2))
        eps <- rmvt(nsim, sigma, df)
        I <- eps[,1]<0
        eps[I,1] <- -sqrt(-eps[I,1])
        z <- sqrt(1-corr^2) * eps
        for(i in 1:(nsim-1)) data[i+1,] <- corr*data[i,] + z[i,]
        data <- data[(burnin+1):nsim,]
      }
    }
    if(type=="ARMA"){
     if(dist=="double-Pareto" & any(copula=="Gaussian", copula=="Gumbel")){
       # Stationary auto-regressive time series with symmetric double Pareto iid innovations
       # Set parameters
       corr <- par$corr
       scale <- par$scale
       shape <- par$shape
       smooth <- par$smooth
       dep <- par$dep
       if(copula=="Gumbel") depCopula <- gumbelCopula(dep)
       if(copula=="Gaussian") depCopula <- normalCopula(dep)
       # Set total number of data
       nsim <- ndata+burnin
       data <- array(0, c(nsim, 2))
       z <- rmadoublepareto(nsim, scale, shape, depCopula)
       z <- sqrt(1-corr^2)*z
       for(i in 1:(nsim-1)) data[i+1,] <- corr*data[i,] + smooth * z[i,] + z[i+1,]
       data <- data[(burnin+1):nsim,]
     }
     if(dist=="ADouble-Pareto" & any(copula=="Gaussian", copula=="Gumbel")){
       # Stationary auto-regressive time series with asymmetric double Pareto iid innovations
       # Set parameters
       corr <- par$corr
       scale <- par$scale
       shape <- par$shape
       smooth <- par$smooth
       dep <- par$dep
       if(copula=="Gumbel") depCopula <- gumbelCopula(dep)
       if(copula=="Gaussian") depCopula <- normalCopula(dep)
       # Set total number of data
       nsim <- ndata+burnin
       data <- array(0, c(nsim, 2))
       eps <- rmadoublepareto(nsim, scale, shape, depCopula)
       I <- eps[,1]<0
       eps[I,1] <- -sqrt(-eps[I,1])
       z <- sqrt(1-corr^2)*eps
       for(i in 1:(nsim-1)) data[i+1,] <- corr*data[i,] + smooth * z[i,] + z[i+1,]
       data <- data[(burnin+1):nsim,]
     }
   }
   if(type=="GARCH"){
     if(dist=="Gaussian" & copula=="Gaussian"){
       # Stationary GARCH time series with Gaussian iid innovations
       alpha <- par$alpha[1:2]
       beta <- par$beta
       dep <- par$dep
       varcov <- matrix(c(1, dep, dep, 1), ncol=2)
       # Set total number of data
       nsim <- ndata+burnin
       data <- array(0, c(nsim,2))
       sigma <- array(0, c(nsim, 2))
       z <- rmvnorm(nsim, sigma=varcov)
       for(i in 1:(nsim-1)){
         sigma[i+1,] <- sqrt(alpha[1] + alpha[2] * data[i,]^2 + beta * sigma[i,]^2)
         data[i+1,] <- sigma[i+1,] * z[i,]
       }
       data <- data[(burnin+1):nsim,]
     }
     if(dist=="Gaussian" & copula=="StudentT"){
       # Stationary GARCH time series with Gaussian iid innovations
       alpha <- par$alpha[1:2]
       beta <- par$beta
       dep <- par$dep
       varcov <- matrix(c(1, dep, dep, 1), ncol=2)
       df <- par$df
       # Set total number of data
       nsim <- ndata+burnin
       data <- array(0, c(nsim,2))
       sigma <- array(0, c(nsim, 2))
       z <- rmvt(nsim, sigma, df)
       for(i in 1:(nsim-1)){
         sigma[i+1,] <- sqrt(alpha[1] + alpha[2] * data[i,]^2 + beta * sigma[i,]^2)
         data[i+1,] <- sigma[i+1,] * z[i,]
       }
       data <- data[(burnin+1):nsim,]
     }
     if(dist=="AGaussian" & copula=="StudentT"){
       # Stationary GARCH time series with Gaussian iid innovations
       alpha <- par$alpha[1:2]
       beta <- par$beta
       dep <- par$dep
       varcov <- matrix(c(1, dep, dep, 1), ncol=2)
       df <- par$df
       # Set total number of data
       nsim <- ndata+burnin
       data <- array(0, c(nsim,2))
       sigma <- array(0, c(nsim, 2))
       u <- pt(rmvt(nsim, varcov, df), df)
       I <- u[,1] <= 0.5
       z <- cbind(-log(2*(1-u[,1])), qnorm(u[,2]))
       z[I,1] <- 2*u[I,1]-1
       for(i in 1:(nsim-1)){
         sigma[i+1,] <- sqrt(alpha[1] + alpha[2] * data[i,]^2 + beta * sigma[i,]^2)
         data[i+1,] <- sigma[i+1,] * z[i,]
       }
       data <- data[(burnin+1):nsim,]
     }
   if(dist=="AGaussian" & copula=="Gumbel"){
     # Stationary GARCH time series with Gaussian iid innovations
     alpha <- par$alpha[1:2]
     beta <- par$beta
     dep <- par$dep
     # Set total number of data
     nsim <- ndata+burnin
     data <- array(0, c(nsim,2))
     sigma <- array(0, c(nsim, 2))
     u <- rCopula(nsim, gumbelCopula(dep))
     I <- u[,1] <= 0.5
     z <- cbind(-log(2*(1-u[,1])), qnorm(u[,2]))
     z[I,1] <- 2*u[I,1]-1
     for(i in 1:(nsim-1)){
       sigma[i+1,] <- sqrt(alpha[1] + alpha[2] * data[i,]^2 + beta * sigma[i,]^2)
       data[i+1,] <- sigma[i+1,] * z[i,]
     }
     data <- data[(burnin+1):nsim,]
   }
 }
  return(data)
}

 #########################################################
 ### END
 ### Main-routines (VISIBLE FUNCTIONS)
 ###
 #########################################################
