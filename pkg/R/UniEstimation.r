#########################################################
### Authors: Simone Padoan and Gilles Stuplfer        ###
### Emails: simone.padoan@unibocconi.it               ###
### gilles.stupfler@ensai.fr                          ###
### Institution: Department of Decision Sciences,     ###
### University Bocconi of Milan, Italy,               ###
### Ecole Nationale de la Statistique et de           ###
### l'Analyse de l'Information, France                ###
### File name: UniEstimation.r                        ###
### Description:                                      ###
### This file contains a set of procedures            ###
### for estimating (point and interval estimation)    ###
### risk measures as Value-At-Risk and Expectile      ###
### for i.i.d. and dependent data in the              ###
### univariate case                                   ###
### Last change: 2020-07-13                           ###
#########################################################


################################################################################
### START
### Sub-routines (HIDDEN FUNCTIONS)
###
################################################################################

# A.1) Defines the so-called expectile check function
etafun <- function(x, tau, u) return(abs(tau-(x<=u))*(x-u)^2)

# A.1.1) Defines the empirical asymmetric squared deviation function
costfun <- function(data, tau, u) return(mean(etafun(data,tau,u)))

# A.2) Defines the so-called quantile check function
varfun <- function(x, tau, u) return(abs(tau-(x<=u))*(x-u))

# A.2.1) Defines the asymmetric weighted mean absolute deviations
acostfun <- function(data, tau, u) return(mean(varfun(data,tau,u)))

# Defines the empirical mean of the quantile check function in A.2)
sacostfun <- function(data, tau, u) return(mean((varfun(data,tau,u))^2))

# Defines the empirical mean of the pairwise product of quantile check functions
pacostfun <- function(I, data, tau, u) {
  return(mean(varfun(data[,I[1]],tau,u)*varfun(data[,I[2]],tau,u)))
}

# Computes the deviance term of the empirical version of the asymptotic variance
devcontrib <- function(i, data, est, meanexc, p, sn){
  sdata <- data[i:(sn+(i-1))]
  res <- sum(sdata[sdata>est] - meanexc) / (est*sqrt(sn*p))
  return(res)
}

# Computes the number of high exceedances
numexceed <- function(i, data, t, rn){
  sdata <- data[i:(rn+(i-1))]
  res <- sum(sdata>t)
  return(res)
}

# Computes the variance as in formula 32 of Drees(2003) Bernoulli
DHVar <- function(data, tau, tau1, j, k, ndata){
  den <- 0
  num <- 0

  # Computes an estimate of the extreme quantile
  extQ <- extQuantile(data, tau, tau1, k=k)$ExtQHat
  # apply formula 32
  for(i in j:k){
    den <- den + (i^(-1/2) - log(k/(ndata*(1-tau1)))/log(i/(ndata*(1-tau1))) * 1/sqrt(k))^2
    iextQ <- extQuantile(data, 1-i/ndata, tau1, k=i)$ExtQHat
    num <- num + (log(iextQ/extQ)/log(i/(ndata*(1-tau1))))^2
  }
  return(num/den)
}

# Defines the log-likelihood for the generalised Pareto model
pllik <- function(par, data, k){
  sigma <- par[1]
  gamma <- par[2]
  llik <- -1e+10

  if(sigma<=0 || gamma<= -0.5) return(llik)

  z <- 1+gamma*data/sigma
  if(any(z<=0)) return(llik)

  llik <- -k*log(sigma) - (1/gamma+1)*sum(log(z))
  if(is.infinite(llik)) llik <- -1e+10
  return(llik)
}

Mka <- function(data, k, a){
  dataord <- sort(data, decreasing=TRUE)
  res <- mean((log(dataord[1:k]) - log(dataord[k+1]))^a)
  return(res)
}

Rka <- function(data, k, a){
  mka <- Mka(data, k, a)
  mk1 <- Mka(data, k, 1)
  mk2 <- Mka(data, k, 2)

  res <- (mka - gamma(a+1) * mk1^a) / (mk2 - 2 * mk1^2)
  return(res)
}

Ska <- function(data, k, a){
  rk2a <- Rka(data, k, 2*a)
  rkap1 <- Rka(data, k, a+1)

  res <- (a * (a+1)^2 * (gamma(a))^2 * rk2a) / (4 * gamma(2 * a) * (rkap1)^2)
  return(res)
}

# Computes the bias term
biasTerm <- function(data, k, gammaHat){
  # Subroutines:
  Sk2 <- function(data, k){
    dataord <- sort(data, decreasing=TRUE)
    z <- log(dataord[1:k]) - log(dataord[k+1])
    mk1 <- mean(z)
    mk2 <- mean(z^2)
    mk3 <- mean(z^3)
    mk4 <- mean(z^4)

    res <- (3/4) * ((mk4 - 24 * mk1^4) * (mk2 - 2 * mk1^2)) / (mk3 - 6 * mk1^3)^2
    return(res)
  }
  RhoHat <- function(data, k){
    sk2 <- Sk2(data, k)
    if(sk2 >= 2/3 & sk2 <= 3/4) res <- (6 * sk2 + sqrt(3 * sk2 - 2) - 4) / (4 * sk2 - 3)
    else res <- -Inf
    return(res)
  }
  # Main body
  m <- sum(data > 0)
  K <- round(min(m-1, (2*m)/log(log(m))))

  I <- array(1:K, c(K,1))
  rho <- apply(I, 1, RhoHat, data=data)

  kr <- max(I[rho != -Inf])
  rhoHat <- rho[kr]

  mk2 <- Mka(data, k, 2)
  # computes important terms
  twoGammaHat <- 2 * gammaHat
  omRhoHat <- 1 - rhoHat
  numerator <- (mk2 - 2 * gammaHat^2)
  # computes the bias term
  bias <- numerator / (twoGammaHat * rhoHat * omRhoHat^(-1))
  # computes the adjustment for the computation of the quantile estimator at the extreme level
  adjust <- numerator * omRhoHat^2 / (twoGammaHat * rhoHat^2)
  return(list(bias=bias, adjust=adjust))
}

################################################################################
###
### Estimation of the expectile estimator variance
### for time series and iid observations
### @ the intermediate level
###
################################################################################
estExpectileVar <- function(data, ndata, tau, est, tailest, varType, bigBlock,
                            smallBlock, k){
  # main body:
  # initialization the return value
  res <- NULL

  # computes an estimate of the tail index
  if(tailest=="Hill") gammaHat <- HTailIndex(data, k)$gammaHat
  if(tailest=="ExpBased") gammaHat <- EBTailIndex(data, tau, est)

  # A) ASSUMES A STATIONARY TIME-SERIES WITH IID OBSERVATIONS
  if(varType %in% c("asym-Ind", "asym-Ind-Rel")){
    # expectile estimator variance using the formula for iid data
    res <- 2 * gammaHat^3 / (1 - 2 * gammaHat)
    if(res<=0 || is.infinite(res)) res <- NA
    return(res)
  }
  if(varType %in% c("asym-Ind-Adj", "asym-Ind-Adj-Rel")){
    # expectile estimator variance using the formula for iid data
    eecdf <- ecdf(data)(est)
    eesf <- 1 - eecdf
    res <- 2 * gammaHat^2 / (1 - 2 * gammaHat) * (eesf + 1 - tau) * (1 - tau) /
           (eesf * tau + eecdf * (1 - tau))^2
    if(res<=0 || is.infinite(res)) res <- NA
    return(res)
  }
  # B) ASSUME A STATIONARY TIME-SERIES WITH DEPENDENT OBSERVATIONS
  # At the moment the asymptotic variance is only available for the LAWS expectile estimator
  # First, computes the sigma^2(gamma, R), i.e. incremental factor of the asymptotic variance due to the dependence
  # See formula in Lemma 5.3 of our article
  # computes the block size and number of blocks
  if(is.null(smallBlock)){
    # this method implements the fact that the estimator in Lemma 5.3 is
    # consistent estimator of the expectile variance (it doesn not use small- and big-block approach)
    # define block size
    sizeBlock <- bigBlock
    # defines the number of blocks
    nBlocks <- ndata-sizeBlock+1
    indx <- array(1:nBlocks,c(nBlocks,1))
  }
  else{
    # this method uses the small- and big-block approach
    sizeBlock <- bigBlock+smallBlock
    indx <- seq(1, ndata, by=sizeBlock)[1:floor(ndata/sizeBlock)]
    indx <- array(indx, c(length(indx),1))
  }
  # computes the mean of exceedances
  meanexc <- mean(data[data>est])
  # computes  the total amount of the normalised expectile exceedances, over the big-blocks of observations
  # See the formula of Lemma 5.3 of our article
  dev <- apply(indx, 1, devcontrib, data=data, est=est, meanexc=meanexc,
               p=(1-tau), sn=sizeBlock)
  # a) COMPUTES THE ASYMPTOTIC VARIANCE ACCORDING TO THE FORMULA OF THEOREM 4.1
  # THIS IS THE STANDARD RESULT
  if(varType=="asym-Dep"){
    adjust <- gammaHat^2
    res <- adjust * var(dev)
    if(res<0 || res==Inf) res <- 0
    return(res)
  }
  # b) COMPUTES THE ASYMPTOTIC VARIANCE ACCORDING TO THE FORMULA OF THEOREM 4.1
  # BUT CONSIDEYING THE ADJUSTED VERSION OF THE STANDARD FORMULA
  # THE ADJUSTMENT TAKES INTO ACCOUNT THE HEAVYNESS OF THE DISTRIBUTION TAIL
  if(varType=="asym-Dep-Adj"){
    seriesDep <-as.numeric(acf(data, plot=FALSE)$acf)
    isStrong <- all(seriesDep[2:25]>=.1)
    if(isStrong){
      if(gammaHat > (1/5)) adjust <- gammaHat^(1/2)
      if((gammaHat > (1/8)) & (gammaHat <= (1/5))) adjust <- gammaHat
      if(gammaHat <= (1/8)) adjust <- gammaHat^2
    }
    else{
      if(gammaHat > (1/3)) adjust <- gammaHat^(1/2)
      if((gammaHat > (1/5)) & (gammaHat <= (1/3))) adjust <- gammaHat
      if(gammaHat <= (1/5)) adjust <- gammaHat^2
    }
    res <- adjust * var(dev)
    if(res<0 || res==Inf) res <- 0
    return(res)
  }
}

################################################################################
###
### Estimation of the Hill estimator variance
### for time series and iid observations
###
###
################################################################################
estHillVar <- function(data, ndata, gammaHat, varType, bigBlock, smallBlock, k){
# Main body:
# computes the asymptotic variance for iid data
if(varType=="asym-Ind") {
  AdjVar <- 1
  mu <- 2
}
# computes the asymptotic variance for serial dependence data
if(varType=="asym-Dep"){
  # computes the dependence component
  t <- as.numeric(quantile(data, 1-k/ndata))
  sizeBlock <- bigBlock+smallBlock
  indx <- seq(1, ndata, by=sizeBlock)[1:floor(ndata/sizeBlock)]
  indx <- array(indx, c(length(indx),1))
  sexc <- apply(indx, 1, numexceed, data=data, t=t, rn=bigBlock)
  AdjVar <- ndata/(bigBlock*k) * var(sexc)
  # set the estimated gamma index power to the stadard value 2
  mu <- 2
}
# computes the asymptotic variance for serial dependence data with adjustment
if(varType=="asym-Dep-Adj"){
  # computes the dependence component
  t <- as.numeric(quantile(data, 1-k/ndata))
  sizeBlock <- bigBlock+smallBlock
  indx <- seq(1, ndata, by=sizeBlock)[1:floor(ndata/sizeBlock)]
  indx <- array(indx, c(length(indx),1))
  sexc <- apply(indx, 1, numexceed, data=data, t=t, rn=bigBlock)
  AdjVar <- ndata/(bigBlock*k) * var(sexc)
  # sets the estimated gamma index power to the ajusted value
  seriesDep <-as.numeric(acf(data, plot=FALSE)$acf)
  isStrong <- all(seriesDep[2:25]>=.1)
  if(isStrong){
    if(gammaHat > (1/5)) mu <- 1/2
    if((gammaHat > (1/8)) & (gammaHat <= (1/5))) mu <- 1
    if(gammaHat <= (1/8)) mu <- 2
  }
  else{
    if(gammaHat > (1/3)) mu <- 1/2
    if((gammaHat > (1/5)) & (gammaHat <= (1/3))) mu <- 1
    if(gammaHat <= (1/5)) mu <- 2
  }
}
# computes the asymptotic variance
res <- gammaHat^mu * AdjVar
return(res)
}

################################################################################
### END
### Sub-routines (HIDDEN FUNCTIONS)
###
################################################################################


################################################################################
### START
### Main-routines (VISIBLE FUNCTIONS)
###
################################################################################

################################################################################
### START
###
################## UNIVARIATE CASE #############################################

################################################################################
###
### Estimation of the tail index gamma using the Hill estimator
### for time series and iid observations
###
###
################################################################################
HTailIndex <- function(data, k, var=FALSE, varType="asym-Dep", bias=FALSE,
                       bigBlock=NULL, smallBlock=NULL, alpha=0.05){
  # initialization
  VarGamHat <- NULL
  CIgamHat <- NULL
  BiasGamHat <- 0
  AdjExtQHat <- 0

  # main body:
  if(is.null(k)) stop("Enter a value for the parameter 'k' ")
  varInd <- varType %in% c("asym-Ind", "asym-Ind-Adj", "asym-Ind-Log",
                           "asym-Ind-Adj-Log")
  if(!any(varType=="asym-Dep", varType=="asym-Dep-Adj", varInd))
  stop("The parameter 'varType' can only be 'asym-Dep', 'asym-Dep-Adj' or 'asym-Ind' ")
  if(varInd) varType <- "asym-Ind"
  # computes the sample size
  ndata <- length(data)
  dataord <- sort(data, decreasing=TRUE)
  gammaHat <- mean(log(dataord[1:k])) - log(dataord[k+1])

  # computes the bias term of the Hill esitmator and the adjustment term
  # for the Weissman quantile estimator
  if(bias) {
    bt <- biasTerm(data, k, gammaHat)
    BiasGamHat <- bt$bias
    AdjExtQHat <- bt$adjust
  }
  # computes the asymptotic variance of the Hill estimator
  if(var) {
    VarGamHat <- estHillVar(data, ndata, gammaHat, varType, bigBlock, smallBlock, k)
    # computes the margin error
    ME <- sqrt(VarGamHat)*qnorm(1-alpha/2) / sqrt(k)
    # defines an approximate (1-alpha)100% confidence interval for the tail index
    CIgamHat <- c((gammaHat-BiasGamHat)-ME, (gammaHat-BiasGamHat)+ME)
  }
  return(list(gammaHat=gammaHat,
              VarGamHat=VarGamHat,
              CIgamHat=CIgamHat,
              BiasGamHat=BiasGamHat,
              AdjExtQHat=AdjExtQHat))
}

################################################################################
###
### Estimation of the tail index gamma using the Maximum Lilelihood (ML)
### estimator, for time series and iid observations
###
###
################################################################################
MLTailIndex <- function(data, k, var=FALSE, varType="asym-Dep", bigBlock=NULL,
                        smallBlock=NULL, alpha=0.05){
  # initialization
  VarGamHat <- NULL
  CIgamHat <- NULL

  # main body:
  if(is.null(k)) stop("Enter a value for the parameter 'k' ")
  if(!any(varType=="asym-Dep", varType=="asym-Ind")) stop("The parameter 'varType' can only be 'asym-Dep' or 'asym-Ind' ")
  # compute the sample size
  ndata <- length(data)
  # derives the ordered data
  dataord <- sort(data, decreasing=TRUE)
  # computes the peaks above a threshold
  z <- dataord[1:k] - dataord[k+1]
  # initialize parameters
  par <- c(5,.5)
  gammaHat <- optim(par, pllik, data=z, k=k, method="Nelder-Mead", control=list(fnscale=-1,
               factr=1, pgtol=1e-14, maxit=1e8))$par[2]

  # compute the ML estimator variance (for time series data)
  if(var){
    AdjVar <- 1
    if(varType=="asym-Dep"){
      t <- as.numeric(quantile(data, 1-k/ndata))
      sizeBlock <- bigBlock+smallBlock
      indx <- seq(1, ndata, by=sizeBlock)[1:floor(ndata/sizeBlock)]
      indx <- array(indx, c(length(indx),1))
      sexc <- apply(indx, 1, numexceed, data=data, t=t, rn=bigBlock)
      AdjVar <- ndata/(bigBlock*k) * var(sexc)
    }
    # computes the asymptotic variance
    VarGamHat <- (1+gammaHat)^2 * AdjVar
    # computes the margin error
    ME <- sqrt(VarGamHat)*qnorm(1-alpha/2) / sqrt(k)
    # defines an approximate (1-alpha)100% confidence interval for the tail index
    CIgamHat <- c(gammaHat-ME, gammaHat+ME)
    }
  return(list(gammaHat=gammaHat,
              VarGamHat=VarGamHat,
              CIgamHat=CIgamHat))
}

################################################################################
###
### Estimation of the tail index gamma using the Moment Estimator
### for time series and iid observations
###
###
################################################################################
MomTailIndex <- function(data, k){
  # main body:
  if(is.null(k)) stop("Enter a value for the parameter 'k' ")
  # derives the ordered data
  dataord <- sort(data, decreasing=TRUE)
  # computes the peaks above a threshold
  z <- log(dataord[1:k]) - log(dataord[k+1])

  M1 <- mean(z)
  M2 <- mean(z^2)

  res <- M1 + 1 - 0.5/(1 - M1^2 / M2)
  return(res)
}

################################################################################
###
### Estimation of the tail index gamma using the Expectile-Based (EB)
### estimator (@ the intermediate level), for time series and iid observations
###
###
################################################################################
EBTailIndex <- function(data, tau, est=NULL){
  # main body:
  if(is.null(tau)) stop("Enter a value for the parameter 'tau' ")
  # computes the exceeding probability
  p <- 1-tau
  # compute an estimate of the expectile if it is not provided
  if(is.null(est)) est <- estExpectiles(data, tau)$ExpctHat
  # computes the empirical distribution function
  decdf <- ecdf(data)
  # evaluate the ecdf at the expectile value
  eecdf <- decdf(est)
  # computes the empirical surival function at the expectile value
  eesf <- 1-eecdf
  # computes an estimate of tje tail index
  res <- (1+eesf/p)^(-1)
  return(res)
}

################################################################################
###
### Estimation of the extreme quantile @ the extreme lelvel tau1
### using the Weissman estimator, for time series and iid observations
###
###
################################################################################
extQuantile <- function(data, tau, tau1, var=FALSE, varType="asym-Dep", bias=FALSE,
                        bigBlock=NULL, smallBlock=NULL, k=NULL, alpha=0.05){
  # initialization
  gammaHat <- NULL
  VarExQHat <- NULL
  CIExtQ <- NULL

  # main body:
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  # computes the sample size
  ndata <- length(data)
  if(isNk) k <- floor(ndata*(1-tau))
  if(isNtau) tau <- 1-k/ndata

  # estimation of the quantile @ the intermediate level based on the
  # empirical quantile
  QHat <- as.numeric(quantile(data, tau))
  # estimation of the tail index and related quantities using the Hill estimator
  if(varType=="asym-Alt-Dep") estHill <- HTailIndex(data, k)
  else estHill <- HTailIndex(data, k, var, varType, bias, bigBlock, smallBlock, alpha)

  # computes an estimate of the tail index with a bias-correction
  gammaHat <- estHill$gammaHat - estHill$BiasGamHat
  # estimation of the quantile @ the extreme level tau1 using the Weissman
  # estimator with a bias-correction
  extQ <- QHat * ((1-tau1)/(1-tau))^(-gammaHat) * (1 - estHill$AdjExtQHat)

  # estimation of the asymptotic of the Hill estimator's variance
  if(var){
    # The default approach for computing the asymptotic variance with serial dependent observations
    # is the method proposed by Drees (2003). In this case it is assumed that there is no bias term
    # If it is assumed that the Hill estimator requires a bias correction then the the asymptotic
    # variance is estimated after correcting the tail index estimate by the bias correction
    VarExQHat <- estHill$VarGamHat

    if((varType=="asym-Alt-Dep") & (!bias)){
      # Drees (2003) approach
      j <- max(2, ceiling(ndata*(1-tau1)))
      VarExQHat <- DHVar(data, tau, tau1, j, k, ndata)
    }
    # computes lower and upper bounds of the (1-alpha)% CI
    K <- sqrt(VarExQHat)*log((1-tau)/(1-tau1))/sqrt(k)
    lbound <- extQ * exp(qnorm(alpha/2)*K)
    ubound <- extQ * exp(qnorm(1-alpha/2)*K)
    CIExtQ <- c(lbound, ubound)
  }

  return(list(ExtQHat=extQ,
              VarExQHat=VarExQHat,
              CIExtQ=CIExtQ))
}

################################################################################
###
### Estimation of the expectile
### @ the intermediate level tau, for time series and iid observations
### LAWS and QB methods are used
### estimated variance and (1-alpha)100% CI is computed
###
################################################################################
estExpectiles <- function(data, tau, method="LAWS", tailest="Hill", var=FALSE,
                          varType="asym-Dep-Adj", bigBlock=NULL, smallBlock=NULL,
                          k=NULL, alpha=0.05){
  # initialization
  ExpctHat <- NULL
  VarExpHat <- NULL
  CIExpct <- NULL
  biasTerm <- 0

  # main body:
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  # computes the sample size
  ndata <- length(data)
  if(isNk) k <- floor(ndata*(1-tau))
  if(isNtau) tau <- 1-k/ndata
  cn <- sqrt(floor(ndata*(1-tau)))

  # Estimation of the expectile at the intermediate level based on the direct LAWS estimator
  if(method=="LAWS"){
    u <- as.numeric(quantile(data, tau))
    ExpctHat <- optim(u, costfun, method="BFGS", tau=tau, data=data)$par
    if(var){
      if(!varType %in% c("asym-Ind","asym-Ind-Adj", "asym-Ind-Adj-Rel") &
      any(is.null(bigBlock), is.null(smallBlock)))
      stop("Insert the value of the big-blocks and small-blocks")
      VarExpHat <- estExpectileVar(data, ndata, tau, ExpctHat, tailest, varType,
                                   bigBlock, smallBlock, k)
      # computes the margin error
      K <- qnorm(1 - alpha / 2) * sqrt(VarExpHat) / cn
      lbound <- ExpctHat / (1 + K)
      ubound <- ExpctHat / (1 - K)
      # defines the (1-alpha)% CI
      CIExpct <- c(lbound, ubound)
    }
  }
  # Estimation of the expectile @ the intermediate level based on the
  # indirect quantile based estimator
  if(method=="QB"){
    # estimates gamma index
    if(tailest=="Hill") gammaHat <- HTailIndex(data, k)$gammaHat
    if(tailest=="ExpBased") gammaHat <- EBTailIndex(data, tau)
    if(gammaHat >= 1){
      warning("The tail index estimate is greater than 1. The QB method can't be applied.")
      return(list(ExpctHat=NA, biasTerm=biasTerm, VarExpHat=NA, CIExpct=NA))
    }
    QHat <- as.numeric(quantile(data, tau))
    ExpctHat <- QHat * (1 / gammaHat - 1)^(-gammaHat)
    if(varType=="asym-Ind-Adj") biasTerm <- -gammaHat * (1 / gammaHat - 1)^gammaHat *
                                            mean(data) * cn / QHat
    # checks whether the asymptotic variance is requested
    if(var){
      if(!varType %in% c("asym-Ind","asym-Ind-Adj","asym-Ind-Adj-Rel")) stop("Invalid value for the asymptotic variance")
      VarExpHat <- gammaHat^2
      if(varType %in% c("asym-Ind-Adj","asym-Ind-Adj-Rel")){
        mg <- 1 / (1 - gammaHat) - log(1 / gammaHat - 1)
        VarExpHat <- VarExpHat * (1 + mg^2)
      }
      # computes standardize standard deviation
      K <- qnorm(1 - alpha / 2) * sqrt(VarExpHat)
      # computes lower and upper bounds of the (1-alpha)100% CI
      lbound <- ExpctHat * 1 / (1 + (biasTerm + K) / cn)
      ubound <- ExpctHat * 1 / (1 + (biasTerm - K) / cn)
      # defines the (1-alpha)% CI
      CIExpct <- c(lbound, ubound)
    }
  }
  return(list(ExpctHat=ExpctHat,
              biasTerm=biasTerm,
              VarExpHat=VarExpHat,
              CIExpct=CIExpct))
}

################################################################################
###
### Estimation of the expectile
### @ the extreme level tau1, for time series and iid observations
### LAWS and QB methods are used
### estimated variance and (1-alpha)100% CI is computed
###
################################################################################
predExpectiles <- function(data, tau, tau1, method="LAWS", tailest="Hill", var=FALSE,
                          varType="asym-Dep", bias=FALSE, bigBlock=NULL, smallBlock=NULL,
                          k=NULL, alpha_n=NULL, alpha=0.05){
  # initialization
  EExpcHat <- NULL
  VarExtHat <- NULL
  CIExpct <- NULL
  HBAdjExtQHat <- 0
  BiasGamHat <- 0
  BiasExtHat <- 0

  # main body:
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  # computes the sample size
  ndata <- length(data)
  if(isNk) k <- floor(ndata*(1-tau))
  if(isNtau) tau <- 1-k/ndata

  # computes an estimate of the tail index using the Hill estimator or
  # the expectile based estimator
  if(tailest=="Hill"){
    # estimation of the tail index and related quantities using the Hill estimator
    estHill <- HTailIndex(data, k, var, varType, bias, bigBlock, smallBlock, alpha)
    gammaHat <- estHill$gammaHat
    BiasGamHat <- estHill$BiasGamHat
    HBAdjExtQHat <- estHill$AdjExtQHat
  }
  if(tailest=="ExpBased") gammaHat <- EBTailIndex(data, tau)
  # checks whether the tail index has been well esitmated
  if(is.na(gammaHat)) return(list(ExpctHat=NA, VarExtHat=NA, CIExpct=NA))

  # estimation of the extreme level if requested
  if(is.null(tau1)) tau1 <- estExtLevel(alpha_n, gammaHat=gammaHat)$tauHat

  # estimation of the expectile @ the extreme level based on the LAWS estimator
  if(method=="LAWS"){
    # computes an estimate of the expectile @ the intermediate level tau:
    ExpcHat <- estExpectiles(data, tau)$ExpctHat
    # computes an estimate of the expectile @ the extreme level tau1:
    EExpcHat <- ExpcHat * ((1-tau1)/(1-tau))^(-gammaHat)
  }
  # estimation of the expectile @ the extreme level based on the QB estimator
  if(method=="QB"){
    # estimation of the quantile @ the intermediate level based on the empirical quantile
    QHat <- as.numeric(quantile(data, tau))
    # estimation of the quantile @ the extreme level tau1 using the Weissman
    # estimator. If requested the bias-correction is implemented
    gammaHat <- gammaHat - BiasGamHat
    extQ <- QHat * ((1-tau1)/(1-tau))^(-gammaHat) * (1 - HBAdjExtQHat)
    # computes an estimate of the expectile @ the extreme level tau1 based on
    # the the Weissman estimator
    if(gammaHat < 1) EExpcHat <- extQ * (1/gammaHat - 1)^(-gammaHat)
    else{
      EExpcHat <- NA
      warning("The tail index estimate is greater than 1. The QB method can't be applied.")
    }
  }
  # computes an estimate of the asymptotic variance of the expecile estimator
  # @ the extreme level
  if(var){
    if(tailest=="ExpBased") stop("The asymptotic variance has not been implemented yet! when estimating the tail index with the expectile based estimator")
    # computes the asymptotic variance for independent and serial dependent data
    VarExtHat <- estHill$VarGamHat
    rn <- log((1-tau)/(1-tau1))
    # variance for the LAWS estimator
    if(varType %in% c("asym-Ind-Adj", "asym-Ind-Adj-Log") & method=="LAWS"){
      QHat <- as.numeric(quantile(data, tau))
      tapp <- (1 / gammaHat - 1)^(gammaHat)
      gsm <- tapp * mean(data) / QHat
      BiasExtHat <- (gammaHat * gsm) / rn * sqrt(k)
      eecdf <- ecdf(data)(ExpcHat)
      eesf <- 1 - eecdf
      VarExpHatInt <- 2 * gammaHat^2 / (1 - 2 * gammaHat) *
                     (eesf + 1 - tau) * (1 - tau) / (eesf * tau + eecdf * (1 - tau))^2
      VarExtHat <- VarExtHat + (2 * gammaHat^3 * tapp) / (rn * (1 - gammaHat)^2) +
      VarExpHatInt / rn^2
    }
    # variance for the QB estimator
    if(varType %in% c("asym-Ind-Adj", "asym-Ind-Adj-Log") & method=="QB"){
      mg <- 1 / (1 - gammaHat) - log(1 / gammaHat - 1)
      VarExtHat <- VarExtHat * (1 + (mg + rn)^2) / rn^2
    }
    if(VarExtHat<=0 || is.infinite(VarExtHat) || is.na(VarExtHat))
      return(list(ExpctHat=EExpcHat, VarExtHat=NA, CIExpct=NA))
    # computes norming constant
    cn <- sqrt(k) / rn
    # compute standardize standard deviation
    K <- qnorm(1 - alpha / 2) * sqrt(VarExtHat)
    # computes lower and upper bounds of the (1-alpha)% CI
    lbound <- EExpcHat * exp(-(BiasExtHat + K) / cn)
    ubound <- EExpcHat * exp(-(BiasExtHat - K) / cn)
    # defines the (1-alpha)% CI
    CIExpct <- c(lbound, ubound)
  }
  return(list(ExpctHat=EExpcHat,
              biasTerm=BiasExtHat,
              VarExtHat=VarExtHat,
              CIExpct=CIExpct))
}

################################################################################
###
### Estimation of the expectile extreme level tau1:= tau1(alpha_n)
### once that an extreme level alpha_n is provided
### estimated variance and (1-alpha)100% CI is computed
###
################################################################################
estExtLevel <- function(alpha_n, data=NULL, gammaHat=NULL, VarGamHat=NULL,
                        tailest="Hill", k=NULL, var=FALSE, varType="asym-Dep",
                        bigBlock=NULL, smallBlock=NULL, alpha=0.05){
  # initialize output
  tauHat <- NULL
  tauVar <- NULL
  tauCI <- NULL
  if(is.null(gammaHat)){
    if(is.null(data)) stop("Insert a data sample")
    if(is.null(k)) stop("insert a value for the intermediate sequence")
    # computes the tail index
    if(tailest=="Hill") {
      res <- HTailIndex(data, k, var, varType, bigBlock=bigBlock,
                        smallBlock=smallBlock)
      gammaHat <- res$gammaHat
      VarGamHat <- res$VarGamHat
    }
    if(tailest=="ML") {
      res <- MLTailIndex(data, k, var, varType, bigBlock=bigBlock,
                        smallBlock=smallBlock)
      gammaHat <- res$gammaHat
      VarGamHat <- res$VarGamHat
    }
    if(tailest=="Moment") gammaHat <- MomTailIndex(data, k)
    if(tailest=="ExpBased") gammaHat <- EBTailIndex(data, 1-k/length(data))
  }
  # computes a point estimates of the extreme level
  tauHat <- 1 - (1 - alpha_n) * gammaHat / (1 - gammaHat)
  if(!is.null(VarGamHat)){
    # computes the variance of the tau estimator using the delta method
    tauVar <- VarGamHat * (alpha_n-1)^2 / (1-gammaHat)^4
    # compute an symptotic confidence interval for the extreme level
    if(!is.null(k)){
      ME <- qnorm(1-alpha/2) * sqrt(tauVar / k)
      tauCI <- c(tauHat - ME, tauHat + ME)
    }
  }
  return(list(tauHat=tauHat,
              tauVar=tauVar,
              tauCI=tauCI))
}


#########################################################
### END
###
################## UNIVARIATE CASE ######################


#########################################################
### END
### Main-routines (VISIBLE FUNCTIONS)
###
#########################################################
