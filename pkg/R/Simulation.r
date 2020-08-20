#########################################################
### Authors: Simone Padoan and Gilles Stuplfer        ###
### Emails: simone.padoan@unibocconi.it               ###
### gilles.stupfler@ensai.fr                          ###
### Institution: Department of Decision Sciences,     ###
### University Bocconi of Milan, Italy,               ###
### Ecole Nationale de la Statistique et de           ###
### l'Analyse de l'Information, France                ###
### File name: Simulation.r                           ###
### Description:                                      ###
### This file contains a set of procedures            ###
### for simulating i.i.d. data from univariate        ###
### and multivariate heavy-tailed parametric          ###
### families of distributions and serial dependent    ###
### data from univariate and multivariate families    ###
### of time series models with heavy-tailed           ###
### marginal disribution                              ###
### Last change: 2020-07-14                           ###
#########################################################


################################################################################
### START
### Sub-routines (HIDDEN FUNCTIONS)
###
################################################################################

rdoublefrechet <- function(ndata, scale, shape){
  coin <- rbinom(ndata, 1, .5)
  data <- (2*coin-1)*rfrechet(ndata, scale=scale, shape=shape)
  return(data)
}

rdoublepareto <- function(ndata, scale, shape){
  coin <- rbinom(ndata, 1, .5)
  data <- (2*coin-1)*scale*(rgpd(ndata, loc=1, scale=1, shape=1))^(1/shape)
  return(data)
}

rmdoublepareto <- function(ndata, scale, shape, sigma){
  coin <- rbinom(ndata, 1, .5)
  u <- pnorm(rmvnorm(ndata, sigma=sigma))
  data <- (2*coin-1)*scale*(1-u)^(-1/shape)
  return(data)
}

rmcopdoublepareto <- function(ndata, dim, copmod, scale, shape){
  coin <- rbinom(ndata, 1, .5)
  data <- u <-  rCopula(ndata, copmod)
  for(i in 1:dim) data[,i] <- (2*coin-1)*scale[i]*(1-u[,i])^(-1/shape[i])
  return(data)
}

rmcopfrechet <- function(ndata, dim, copmod, scale, shape){
  data <- u <-  rCopula(ndata, copmod)
  for(i in 1:dim) data[,i] <- scale[i]*(-log(u[,i]))^(-1/shape[i])
  return(data)
}

rmcopdoublefrechet <- function(ndata, dim, copmod, scale, shape){
  coin <- rbinom(ndata, 1, .5)
  data <- u <-  rCopula(ndata, copmod)
  for(i in 1:dim) data[,i] <- (2*coin-1)*scale[i]*(-log(u[,i]))^(-1/shape[i])
  return(data)
}


################################################################################


################################################################################
### START
### Main-routines (VISIBLE FUNCTIONS)
###
################################################################################

rtimeseries <- function(ndata, dist="studentT", type="AR", par, burnin=1e+03)
{
  # main body
  # Check whether the distribution in input is available
  if(!(dist %in% c("double-Frechet", "double-Pareto", "Frechet", "Gaussian",
                  "Pareto", "studentT"))) stop("insert the correct DISTRIBUTION!")

  # Set output
  res <- NULL
  # consider the class of stationary sequence with Independent and Identical Distributions
  if(type=="IID"){
    # IID realizations from a Frechet distribution
    if(dist=="Frechet"){
      scale <- par[1]
      shape <- par[2]
      data <- rfrechet(ndata, scale=scale, shape=shape)
    }
    # IID realizations from a Pareto distribution
    if(dist=="Pareto"){
      scale <- par[1]
      shape <- par[2]
      data <- scale*(rgpd(ndata, loc=1, scale=1, shape=1))^(1/shape)
    }
    # IID realizations from a Student-t distribution
    if(dist=="studentT") data <- rt(ndata, par)
  }
  # consider the class of Auto-Regressive time series models
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
       z <- rmcopdoublepareto(nsim, 2, depCopula, scale, shape)
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
       eps <- rmcopdoublepareto(nsim, 2, depCopula, scale, shape)
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

 rmdata <- function(ndata, dist="studentT", copula="studentT", par)
 {
   # main body
   # Check whether the distribution in input is available
   if(!(dist %in% c("studentT", "AstudentT", "TStudentT", "ATStudentT", "double-Pareto", "double-Frechet", "Frechet", "Gaussian"))) stop("insert the correct DISTRIBUTION!")
   # initialization output
   res <- NULL
   # list of possible models
     if(dist=="studentT" & copula=="studentT"){
       # Stationary series of Student-t iid observations on R^d
       df <- par$df
       sigma <- par$sigma
       data <- rmvt(ndata, sigma, df)
     }
     if(dist=="studentT" & copula=="None"){
       # Stationary series of Student-t iid observations on R^d
       df <- par$df
       dimData <- par$dim
       data <- replicate(dimData, rt(ndata, df))
     }
     if(dist=="studentT" & copula=="Gaussian"){
       # Stationary series of Student-t iid observations on R^d
       df <- par$df
       sigma <- par$sigma
       data <- qt(pnorm(rmvnorm(ndata, sigma=sigma)), df)
     }
     if(dist=="AstudentT" & copula=="studentT"){
       # Stationary series of Student-t iid observations on R^d
       df <- par$df
       shape <- par$shape
       sigma <- par$sigma
       data <- rmvt(ndata, sigma, df)
       I <- data[,1] > 0
       data[I,1] <- data[I,1]^(df/shape)
       data[!I,1] <- -(-data[!I,1])^(df/shape)
     }
     if(dist=="TStudentT" & copula=="studentT"){
       # Stationary series of Student-t iid observations on R^d_+
       df <- par$df
       sigma <- par$sigma
       dimData <- nrow(sigma)
       lower <- rep(0, dimData)
       upper <- rep(Inf, dimData)
       data <- rtmvt(ndata, sigma=sigma, df=df, lower=lower, upper=upper)
     }
     if(dist=="AstudentT" & copula=="Gaussian"){
       # Stationary series of Student-t iid observations on R^d
       df <- par$df
       shape <- par$shape
       sigma <- par$sigma
       data <- qt(pnorm(rmvnorm(ndata, sigma=sigma)), df)
       I <- data[,1] > 0
       data[I,1] <- data[I,1]^(df/shape)
       data[!I,1] <- -(-data[!I,1])^(df/shape)
     }
     if(dist=="Frechet" & copula=="None"){
       # Stationary series of Frechet iid observations on R^d_+
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       data <- replicate(dimData, rfrechet(ndata, scale=scale, shape=shape))
     }
     if(dist=="Frechet" & copula=="Clayton"){
       # Stationary series of Frechet iid observations on R^d_+
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- claytonCopula(dep, dimData)
       data <- rmcopfrechet(ndata, dimData, copmod, scale, shape)
     }
     if(dist=="Frechet" & copula=="Gumbel"){
       # Stationary series of Frechet iid observations on R^d_+
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- gumbelCopula(dep, dimData)
       data <- rmcopfrechet(ndata, dimData, copmod, scale, shape)
     }
     if(dist=="Frechet" & copula=="Frank"){
       # Stationary series of Frechet iid observations on R^d_+
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- frankCopula(dep, dimData)
       data <- rmcopfrechet(ndata, dimData, copmod, scale, shape)
     }
     if(dist=="double-Pareto" & copula=="Gumbel"){
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- gumbelCopula(dep, dimData)
       data <- rmcopdoublepareto(ndata, dimData, copula, scale, shape)
     }
     if(dist=="double-Pareto" & copula=="Clayton"){
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- claytonCopula(dep, dimData)
       data <- rmcopdoublepareto(ndata, dimData, copula, scale, shape)
     }
     if(dist=="double-Pareto" & copula=="Frank"){
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- frankCopula(dep, dimData)
       data <- rmcopdoublepareto(ndata, dimData, copula, scale, shape)
     }
     if(dist=="double-Frechet" & copula=="Gumbel"){
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- gumbelCopula(dep, dimData)
       data <- rmcopdoublefrechet(ndata, dimData, copmod, scale, shape)
     }
     if(dist=="double-Frechet" & copula=="Clayton"){
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- claytonCopula(dep, dimData)
       data <- rmcopdoublefrechet(ndata, dimData, copmod, scale, shape)
     }
     if(dist=="double-Frechet" & copula=="Frank"){
       dep <- par$dep
       dimData <- par$dim
       scale <- par$scale
       shape <- par$shape
       copmod <- frankCopula(dep, dimData)
       data <- rmcopdoublefrechet(ndata, dimData, copmod, scale, shape)
     }
  return(data)
}


 ################################################################################
 ### END
 ### Main-routines (VISIBLE FUNCTIONS)
 ###
 ################################################################################
