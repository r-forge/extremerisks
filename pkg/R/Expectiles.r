#########################################################
### Authors: Simone Padoan and Gilles Stuplfer        ###
### Emails: simone.padoan@unibocconi.it               ###
### gilles.stupfler@ensai.fr                          ###
### Institution: Department of Decision Sciences,     ###
### University Bocconi of Milan, Italy,               ###
### Ecole Nationale de la Statistique et de           ###
### l'Analyse de l'Information, France                ###
### File name: Expectiles.r                           ###
### Description:                                      ###
### This file contains a set of routines              ###
### to compute the theoretical expectiles             ###
### for different families of parametric models       ###
### for i.i.d. and serial dependent observations      ###
### Last change: 2020-02-28                           ###
#########################################################

#########################################################
### START
### Sub-routines (HIDDEN FUNCTIONS)
###
#########################################################

# Compute the cost function for the GPD distribution
gpdcostfun <- function(x, scale, shape, tau){
  mu <- scale/(1-shape)
  pmx <- pmean(x,scale,shape)
  pgx <- pgpd(x,scale=scale,shape=shape)

  ppx <- pmx - x*pgx
  res <- ppx/(2*ppx + (x-mu))

  return(res-tau)
}
# Compute the wighted mean
pmean <- function(x, scale, shape){
  y <- scale * pgpd(x,scale=scale,shape=shape)/(1-shape) - x*(1-pgpd(x,scale=scale,shape=shape))/(1-shape)
  return(y)
}

# Approximate the true expectile via Monte Carlo approximation

# 1) Case: IID data from parametric families
# Frechet
expect_frec_iid <- function(ndata, tau, scale, shape, estMethod){
  data <- rfrechet(ndata, scale=scale, shape=shape)
  res <- estExpectiles(data, tau, estMethod)$ExpctHat
  return(res)
}
# Pareto
expect_par_iid <- function(ndata, tau, shape, estMethod){
  data <- (rgpd(ndata, scale=1, loc=1, shape=1))^(1/shape)
  res <- estExpectiles(data, tau, estMethod)$ExpctHat
  return(res)
}
# GPD
expect_gpd_iid <- function(ndata, tau, scale, shape, estMethod){
  data <- rgpd(ndata, scale=scale, shape=shape)
  res <- estExpectiles(data, tau, estMethod)$ExpctHat
  return(res)
}
# student-t
expect_std_iid <- function(ndata, tau, df, estMethod){
  data <- rt(ndata, df)
  res <- estExpectiles(data, tau, estMethod)$ExpctHat
  return(res)
}

# 2) Case: time serie from parametric families
expect_std_ts <- function(ndata, burnin, corr, df, smooth, nsim, tau, estMethod){
  data <- rep(0, nsim)
  z <- sqrt(1-corr^2) * rt(nsim, df)
  for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + smooth * z[i] + z[i+1]
  res <- estExpectiles(data[(burnin+1):ndata], tau, estMethod)$ExpctHat
 return(res)
}

# double Frechet innovations
expect_dfrec_ts <- function(ndata, burnin, corr, scale, shape, smooth, nsim, tau, estMethod){
  data <- rep(0, nsim)
  z <- sqrt(1-corr^2) * rdoublefrechet(nsim, scale=scale, shape=shape)
  for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + smooth * z[i] + z[i+1]
  res <- estExpectiles(data[(burnin+1):ndata], tau, estMethod)$ExpctHat
  return(res)
}

# double Pareto innovations
expect_dpareto_ts <- function(ndata, burnin, corr, scale, shape, smooth, nsim, tau, estMethod){
  data <- rep(0, nsim)
  z <- sqrt(1-corr^2) * rdoublepareto(nsim, scale=scale, shape=1/shape)
  for(i in 1:(nsim-1)) data[i+1] <- corr*data[i] + smooth * z[i] + z[i+1]
  res <- estExpectiles(data[(burnin+1):ndata], tau, estMethod)$ExpctHat
  return(res)
}

# maxima auto-regressive with Frechet innovations
expect_armax_ts <- function(ndata, burnin, corr, scale, shape, nsim, tau, estMethod){
  data <- rep(0, nsim)
  z <- (1-corr)^(1/shape) * rfrechet(nsim, scale=scale, shape=shape)
  for(i in 1:(nsim-1)) data[i+1] <- max((corr)^(1/shape) * data[i],  z[i])
  res <- estExpectiles(data[(burnin+1):ndata], tau, estMethod)$ExpctHat
  return(res)
}

# GARCH model
expect_garch_ts <- function(ndata, burnin, alpha0, alpha, beta, tau, estMethod){
  nsim <- ndata+burnin
  data <- rep(0, nsim)
  sigma <- rep(0, nsim)
  z <- rnorm(nsim)
  for(i in 1:(nsim-1)){
    sigma[i+1] <- sqrt(alpha[1] + alpha[2] * data[i]^2 + beta * sigma[i]^2)
    data[i+1] <- sigma[i+1] * z[i]
  }
  data <- data[(burnin+1):nsim]
  res <- estExpectiles(data, tau, estMethod)$ExpctHat
  return(res)
}

#########################################################
### END
### Sub-routines (HIDDEN FUNCTIONS)
###
#########################################################


#########################################################
### START
### Main-routines (VISIBLE FUNCTIONS)
###
#########################################################

expectiles <- function(par, tau, tsDist="gPareto", tsType="IID", trueMethod="true",
                       estMethod="LAWS", nrep=1e+05, ndata=1e+06, burnin=1e+03){
  # main body
  # Check whether the distribution in input is available
  if(!(tsDist %in% c("studentT", "Frechet", "Pareto", "gPareto", "double-Frechet",
                     "double-Pareto", "Gaussian"))) stop("insert the correct DISTRIBUTION!")
  # Set output
  res <- NULL
  if(trueMethod=="true"){
    # STANDARD PARETO DISTRIBUTION
    if (tsDist == "Pareto"){
      shape <- 1/par[1]
      if (tau < 0.5){
        low <- 0
        up <- 1/(1 - shape)
      }
      else{
        low <- 1/(1 - shape)
        up <- 10*(1/shape-1)^(-shape) * ((1-tau)^(-shape)-1)/shape
      }
        res <- 1 + shape * uniroot(gpdcostfun, c(low, up), scale = 1,
                                   shape = shape, tau = tau)$root
    }
    # GENERALISED PARETO DISTRIBUTION
    if(tsDist=="gPareto"){
      # THEORETICAL EXPECTILES FOR PARETO MARGINAL DISTIBUTION
      # SEE JONES'S PAPER FORMULA 1.1
      scale <- par[1]
      shape <- par[2]
      if(tau<0.5){
        low <- 0
        up <- scale/(1-shape)
      }
      else {
        low <- scale/(1-shape)
        up <- 10*(1/shape-1)^(-shape) * scale*((1-tau)^(-shape)-1)/shape
      }
      res <- uniroot(gpdcostfun, c(low,up), scale=scale, shape=shape, tau=tau)$root
    }
    # NON-CENTERED STUDENT-T DISTRIBUTION
    if(tsDist=="studentT"){
      df <- par[1]
      res <- (df-1)^(-1/df) * qt(tau,df=df)
    }
  }
  if(trueMethod=="approx"){
    if(tsDist=="studentT"){
      # Stationary auto-regressive time series with iid student-t innovations
      if(tsType=="AR"){
        corr <- par[1]
        df <- par[2]
        smooth <- 0
        nsim <- ndata+burnin
        res <- replicate(nrep,expect_std_ts(ndata, burnin, corr, df, smooth, nsim, tau, estMethod))
        res <- mean(res)
      }
      if(tsType=="ARMA"){
        corr <- par[1]
        df <- par[2]
        smooth <- par[3]
        nsim <- ndata+burnin
        res <- replicate(nrep,expect_std_ts(ndata, burnin, corr, df, smooth, nsim, tau, estMethod))
        res <- mean(res)
      }
      # Stationary time series with iid student-t innovations
      if(tsType=="IID"){
        df <- par[1]
        res <- replicate(nrep, expect_std_iid(ndata, tau, df, estMethod))
        res <- mean(res)
      }
    }
    if(tsDist=="double-Frechet"){
      # Stationary auto-regressive time series with double-frechet iid innovations
      if(tsType=="AR"){
        corr <- par[1]
        scale <- par[2]
        shape <- par[3]
        smooth <-0
        nsim <- ndata+burnin
        res <- replicate(nrep,expect_dfrec_ts(ndata, burnin, corr, scale, shape, smooth, nsim, tau, estMethod))
        res <- mean(res)
      }
      if(tsType=="ARMA"){
        corr <- par[1]
        scale <- par[2]
        shape <- par[3]
        smooth <-par[4]
        nsim <- ndata+burnin
        res <- replicate(nrep,expect_dfrec_ts(ndata, burnin, corr, scale, shape, smooth, nsim, tau, estMethod))
        res <- mean(res)
      }
    }
    if(tsDist=="double-Pareto"){
      # Stationary auto-regressive time series with double-frechet iid innovations
      if(tsType=="AR"){
        corr <- par[1]
        scale <- par[2]
        shape <- par[3]
        smooth <- 0
        nsim <- ndata+burnin
        res <- replicate(nrep,expect_dpareto_ts(ndata, burnin, corr, scale, shape, smooth, nsim, tau, estMethod))
        res <- mean(res)
      }
      if(tsType=="ARMA"){
        corr <- par[1]
        scale <- par[2]
        shape <- par[3]
        smooth <- par[4]
        nsim <- ndata+burnin
        res <- replicate(nrep,expect_dpareto_ts(ndata, burnin, corr, scale, shape, smooth, nsim, tau, estMethod))
        res <- mean(res)
      }
    }
    if(tsDist=="Frechet"){
      # Stationary auto-regressione time series with maxima innovations Frechet distributed
      if(tsType=="ARMAX"){
        corr <- par[1]
        scale <- par[2]
        shape <- par[3]
        nsim <- ndata+burnin
        res <- replicate(nrep,expect_armax_ts(ndata, burnin, corr, scale, shape, nsim, tau, estMethod))
        res <- mean(res)
      }
      # Stationary time series with iid components Frechet distributed
      if(tsType=="IID"){
        scale <- par[1]
        shape <- par[2]
        res <- replicate(nrep, expect_frec_iid(ndata, tau, scale, shape, estMethod))
        res <- mean(res)
      }
    }
    # Stationary time series with iid components Generalised Pareto distributed
    if(tsDist=="gPareto"){
      if(tsType=="IID") {
        scale <- par[1]
        shape <- par[2]
        res <- replicate(nrep, expect_gpd_iid(ndata, tau, scale, shape, estMethod))
        res <- mean(res)
    }}
    if(tsDist=="Pareto"){
      if(tsType=="IID"){
        shape <- par[1]
        res <- replicate(nrep, expect_par_iid(ndata, tau, shape, estMethod))
        res <- mean(res)
    }}
    if(tsDist=="Gaussian"){
      if(tsType=="GARCH"){
        alpha <- par[1:2]
        beta <- par[3]
        res <- replicate(nrep, expect_garch_ts(ndata, burnin, alpha, beta, tau, estMethod))
        res <- mean(res)
      }
    }
  }
  return(res)
}

#########################################################
### END
### Main-routines (VISIBLE FUNCTIONS)
###
#########################################################
