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
### Last change: 2020-02-28                           ###
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
       alpha <- par[1:2]
       beta <- par[3]
       data <- garch.sim(alpha=alpha, beta=beta, n=ndata, ntrans=burnin)
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

 #########################################################
 ### END
 ### Main-routines (VISIBLE FUNCTIONS)
 ###
 #########################################################
