#########################################################
### Authors: Simone Padoan and Gilles Stuplfer        ###
### Emails: simone.padoan@unibocconi.it               ###
### gilles.stupfler@ensai.fr                          ###
### Institution: Department of Decision Sciences,     ###
### University Bocconi of Milan, Italy,               ###
### Ecole Nationale de la Statistique et de           ###
### l'Analyse de l'Information, France                ###
### File name: MultiEstimation.r                      ###
### Description:                                      ###
### This file contains a set of procedures            ###
### for estimating (point and interval estimation)    ###
### risk measures as Value-At-Risk and Expectile      ###
### for i.i.d. and dependent data for the             ###
### multivariate case                                 ###
### Last change: 2020-07-13                           ###
#########################################################


#########################################################
### START
### Sub-routines (HIDDEN FUNCTIONS)
###
#########################################################

################################################################################
###
### Computation of the ellipse corresponding to a bivariate normal
### distribution, provided the mean vector and the 2x2
### variance-covariance matrix
###
################################################################################
ellipse <- function(mean=c(0,0), varcov=matrix(c(1,0,0,1),2,2), alpha=0.05, ngrid=250)
{
  ##############################################################################
  # 1) alpha in (0,1) such that (1-alpha) defines the confidence level
  # 2) mean defines the center of the multivariate normal
  # 3) varcov defines the variance-covariance of the multivariate normal
  # 4) ngrid gives the number of points to use for the graphical of the ellipse
  ##############################################################################
  # defines the Mahalanobis distance
  d <- sqrt(qchisq(1-alpha, 2))
  # defines the angles
  theta <- seq(0, 2*pi, length.out=ngrid)
  # computes a circle of radius d
  x <- d * cbind(cos(theta), sin(theta))
  # Spectral decomposition of a variance-covariance matrix
  eig <- eigen(varcov)
  # combines the magnitudes (scaling) and the rotation associated to varcov
  sp <- eig$vec %*% diag(sqrt(eig$values))
  # computes coordinates of the ellipse
  ell <- t(mean - (sp %*% t(x)))
  return(ell)
}

################################################################################
###
### Computation of the ellipsoid corresponding to a trivariate normal
### distribution, provided the mean vector and the 3x3
### variance-covariance matrix
###
################################################################################
ellipsoid <- function(mean=c(0,0,0), varcov=matrix(c(1,0,0,0,1,0,0,0,1),3,3),
                      alpha=0.05, ngrid=60)
{
  ##############################################################################
  # 1) alpha in (0,1) such that (1-alpha) defines the confidence level
  # 2) mean defines the center of the multivariate normal
  # 3) varcov defines the variance-covariance of the multivariate normal
  # 4) ngrid gives the number of points to use for the graphical of the ellipsoid
  ##############################################################################
  # defines subroutine
  EucCoord <- function(x) return(c(cos(x[1])*sin(x[2]), sin(x[1])*sin(x[2]), cos(x[2])))
  # defines the Mahalanobis distance
  d <- sqrt(qchisq(1-alpha, 2))
  # defines the angles
  theta <- seq(0, 2*pi, length.out=ngrid)
  # computes a sphere of radius d
  x <- d * apply(expand.grid(theta,theta), 1, EucCoord)
  # Eigendecomposition of a variance-covariance matrix
  eig <- eigen(varcov)
  # combines the magnitude (scaling) and the rotation associated to varcov
  sp <- eig$vec %*% diag(sqrt(eig$values))
  # computes coordinates of the ellipse
  ell <- t(mean - (sp %*% x))
  return(ell)
}

################################################################################
###
### Inspection whether a values falls inside the ellipsoid (ellipse)
### for a given the mean vector and the 2x2
### variance-covariance matrix
###
################################################################################
isInsideEllipse  <- function(dim=2, varcov=diag(1, dim), alpha=0.05, est)
{
  res <- FALSE
  # inverse square root of covariance matrix
  invSqrtVarCov <- sqrtm(varcov, kmax = 20, tol = .Machine$double.eps^(1/2))$Binv
  # transformation to standard normal
  # est is the log of the estimate divided by true value or the relative estimate
  Z <- invSqrtVarCov %*% est
  S <- sum(Z^2, na.rm=TRUE)
  if(is.na(S)) return(NA)
  # checks if this is within the relevant ball
  if (S <= qchisq(1 - alpha, dim)) res <- TRUE
  return(res)
}

# empirical joint exceeding probability
empTailProb <- function(data, x, ndata){
  return(sum(data[,1] > x[1] & data[,2] > x[2])/ndata)
}

# pairwise empirical joint exceeding probability
empPairCov <- function(indx, data, x, stDev, ndata){
  return(empTailProb(data[, indx], x, ndata) * stDev[indx[1]]* stDev[indx[2]])
}

estCovExpInt <- function(data, ndata, gamma, c, k){
  rdata <- ndata * data / k
  I <- rdata[,1] <= c[1] & rdata[,2] <= c[2]
  res <- sum(((rdata[,1] / c[1])^(-gamma[1]) - 1) *
            ((rdata[,2] / c[2])^(-gamma[2]) - 1) * I) / k

  return(res)
}

estPairCovExpInt <- function(indx, data, ndata, gamma, c, k){
  return(estCovExpInt(data[,indx], ndata, gamma[indx], c[indx], k))
}

intLeftEmpTailCopula <- function(data, ndata , k){
  rdata <- ndata * data / k
  I <- rdata[,1] <= 1 & rdata[,2] <= 1
  res <- sum(log(1/rdata[,1]) * I) / k
  return(res)
}

estPairLeftETC <- function(indx, data, ndata, k){
  return(intLeftEmpTailCopula(data[,indx], ndata, k))
}

intRightEmpTailCopula <- function(data, ndata , k){
  rdata <- ndata * data / k
  I <- rdata[,1] <= 1 & rdata[,2] <= 1
  res <- sum(log(1/rdata[,2]) * I) / k
  return(res)
}

estPairRightETC <- function(indx, data, ndata, k){
  return(intRightEmpTailCopula(data[,indx], ndata, k))
}

intEmpTailCopula <- function(data, ndata , k){
  rdata <- ndata * data / k
  I <- rdata[,1] <= 1 & rdata[,2] <= 1
  res <- sum(I) / k
  return(res)
}

estPairETC <- function(indx, data, ndata, k){
  return(intEmpTailCopula(data[,indx], ndata, k))
}

estAsymCov <- function(data, k, stDev){
  # derives dimensions
  dimData <- dim(data)
  # computes marginal empirical distribution functions
  mecdf <- apply(data,2,ecdf)
  # defines ranks
  rdata <- NULL
  for(i in 1:dimData[2]) rdata <- cbind(rdata, mecdf[[i]](data[,i]))
  # defines the pairwise combinations
  indx <- t(combn(dimData[2],2))
  # defines threhold
  x <- c(1-k/dimData[1], 1-k/dimData[1])
  # computes approximate tail copula
  res <- apply(indx, 1, empPairCov, data=rdata, x=x, stDev=stDev, ndata=dimData[1])

  return(dimData[1] * res / k)
}

################################################################################
###
### Estimation of the multivariate expectile estimator variance-covariance
### matrix @ the intermediate level
### given a sample of iid high-dimnensional observations
###
################################################################################
estMultiExpectVar <- function(data, dimData, ExpctHat, gammaHat, method, k, tau,
                              VarEHat, varType){
  # main body:
  # initialization of important quantities
  CovEHat <- NULL
  VarCovEHat <- NULL
  # A) computes the variance diagonal terms for the variance-covariance matrix
  # for the expectile estimator
  VarCovEHat <- diag(VarEHat)
  # a.1) computes the number of distinct pairs
  indx <- t(combn(dimData[2],2))
  # B) computes the off-diagonal covariance terms of the variance-covariance
  #    matrix for the expectile estimator
  # B.1) consider the independence case
  if(varType %in% c("asym-Ind", "asym-Ind-Rel")) CovEHat <- rep(0, nrow(indx))
  # B.2) computes the off-diagonal covariance of the LAWS estimator
  #      using the proposed adjustment based on dependence observations
  if(varType %in% c("asym-Ind-Adj", "asym-Ind-Adj-Rel") & method=="LAWS"){
    # B.2.1) computes the empirical marginals asymmetric cost functions
    cdata <- data - apply(array(ExpctHat, c(1,dimData[2])), 2, rep, times=dimData[1])
    mij <- apply(cdata, 2, acostfun, tau=tau, u=0)
    # B.2.2) computes the pairwise empirical asymmetric marginals cost functions
    mijkl <- apply(indx, 1, pacostfun, data=cdata, tau=tau, u=0)
    # B.2.3) computes the covariance terms
    CovEHat <- gammaHat[indx[,1]] * gammaHat[indx[,2]] * (mijkl - mij[indx[,1]] * mij[indx[,2]]) /
    ((1-tau) * ExpctHat[indx[,1]] * ExpctHat[indx[,2]])
  }
  # B.3) computes the off-diagonal covariance of the QB estimator
  #      using the proposed adjustment based on dependence observations
  if(varType %in% c("asym-Ind-Adj", "asym-Ind-Adj-Rel") & method=="QB"){
    rdata <- NULL
    # B.3.1) computes marginal emprical distribution functions
    mecdf <- apply(data, 2, ecdf)
    # B.3.2) computes marginal empirical survival functions
    for(i in 1:dimData[2])
      rdata <- cbind(rdata, 1 - dimData[1] * mecdf[[i]](data[, i]) / (dimData[1] + 1))
    mg <- 1 / (1 - gammaHat) - log(1 / gammaHat - 1)
    # B.3.3) computes the covariance terms
    R11 <- apply(indx, 1, estPairETC, data=rdata, ndata=dimData[1],k=k)
    Rj1 <- apply(indx, 1, estPairLeftETC, data=rdata, ndata=dimData[1],k=k)
    R1l <- apply(indx, 1, estPairRightETC, data=rdata, ndata=dimData[1],k=k)
    # B.3.4) covariance of the normalised estimator
    CovEHat <- gammaHat[indx[,1]] * gammaHat[indx[,2]] * (R11 * (1 - mg[indx[,1]]) *
               (1 - mg[indx[,2]]) + mg[indx[,1]] * Rj1 + mg[indx[,2]] * R1l)
  }
  # C) fills in the variance-covariance matrix
  VarCovEHat[lower.tri(VarCovEHat)] <- CovEHat
  VarCovEHat <- t(VarCovEHat)
  VarCovEHat[lower.tri(VarCovEHat)] <- CovEHat
  # C.1) with the relative estimator the variance-covariance matrix needs
  # to be rescaled by the expectile estimator
  if(regexpr("Rel", varType, fixed=TRUE)[1]==-1){
    diag(VarCovEHat) <- ExpctHat^2 * VarEHat
    CovEHat <- ExpctHat[indx[,1]] * ExpctHat[indx[,2]] * CovEHat
    VarCovEHat[lower.tri(VarCovEHat)] <- CovEHat
    VarCovEHat <- t(VarCovEHat)
    VarCovEHat[lower.tri(VarCovEHat)] <- CovEHat
  }
  # C.2) Normalised variance-covariance matrix
  VarCovEHat <- VarCovEHat / k
  return(VarCovEHat)
}

################################################################################
###
### Estimation of the multivariate expectile estimator variance-covariance
### matrix @ the extreme level
### given a sample of iid high-dimnensional observations
###
################################################################################
predMultiExpectVar <- function(data, dimData, ExpctHat, gammaHat, method, k,
                                tau, tau1, VarEHat, varType){
  # main body:
  # initialization of important quantities
  CovEHat <- NULL
  VarCovEHat <- NULL
  # scaling factor
  rn <- log((1-tau)/(1-tau1))
  # A) computes diagonal variance terms of the variance-covariance matrix
  # of the expectile estimator
  VarCovEHat <- diag(VarEHat)
  # A.1) computes the number of distinct pairs
  indx <- t(combn(dimData[2],2))
  # B) computes the off-diagonal covariance terms of the variance-covariance
  #    matrix for the expectile estimator
  # B.1) consider the independence case
  if(varType %in% c("asym-Ind", "asym-Ind-Log")) CovEHat <- rep(0, nrow(indx))
  # B.2) computes the off-diagonal covariance of the LAWS estimator
  #      using the proposed adjustment based on dependence observations
  if(varType %in% c("asym-Ind-Adj", "asym-Ind-Adj-Log") & method=="LAWS"){
    rdata <- NULL
    I <- NULL
    # B.2.1) computes the marginal empirical distribution functions
    mecdf <- apply(data, 2, ecdf)
    # B.2.2) computes the marginal empirical quantile functions
    qHat <- apply(data, 2, quantile, probs=tau)
    for(i in 1:dimData[2]){
      # B.2.3) computes the ranks
      rdata <- cbind(rdata, 1 - dimData[1] * mecdf[[i]](data[, i]) / (dimData[1] + 1))
      I <- cbind(I, data[, i] > qHat[i])
    }
    # B.2.4) computes the empirical asymmetric marginals cost functions
    cdata <- data - apply(array(ExpctHat, c(1,dimData[2])), 2, rep, times=dimData[1])
    mij <- apply(cdata, 2, acostfun, tau=tau, u=0)
    # B.2.5) computes the pairwise asymmetric marginals cost functions
    mijkl <- apply(indx, 1, pacostfun, data=cdata, tau=tau, u=0)
    # B.2.6) computes the off diagonal covariance terms @ the intermediate case
    CovEHatInt <- gammaHat[indx[,1]] * gammaHat[indx[,2]] * (mijkl - mij[indx[,1]] * mij[indx[,2]]) /
    ((1-tau) * ExpctHat[indx[,1]] * ExpctHat[indx[,2]])
    # B.2.7) computes the tail dependence copula
    R11 <- apply(indx, 1, estPairETC, data=rdata, ndata=dimData[1], k=k)
    # B.2.8) computes the Sigma matrices
    varphi <- apply(cdata, 2, varfun, tau=tau, u=0)
    S12 <- S21 <- NULL
    for(i in 1:nrow(indx)){
      S12 <- c(S12, (gammaHat[indx[i,2]] * mean((log(data[I[,indx[i,1]],indx[i,1]]) -
               log(qHat[indx[i,1]])) * varphi[I[,indx[i,1]],indx[i,2]]) -
               gammaHat[indx[i,1]] * gammaHat[indx[i,2]] * mean(varphi[I[,indx[i,1]],indx[i,2]]))/
               ((1-tau)*ExpctHat[indx[i,2]]))
      S21 <- c(S21, (gammaHat[indx[i,1]] * mean((log(data[I[,indx[i,2]],indx[i,2]]) -
               log(qHat[indx[i,2]])) * varphi[I[,indx[i,2]],indx[i,1]]) -
               gammaHat[indx[i,2]] * gammaHat[indx[i,1]] * mean(varphi[I[,indx[i,2]],indx[i,1]]))/
               ((1-tau)*ExpctHat[indx[i,1]]))
    }
    # B.2.9) computes the asymptotic covariance terms
    CovEHat <- gammaHat[indx[,1]] * gammaHat[indx[,2]] * R11 + CovEHatInt / rn^2 +
     (S12 + S21) / rn
  }
  # B.3) computes the off-diagonal covariance of the QB estimator
  #      using the proposed adjustment based on dependence observations
  if(varType %in% c("asym-Ind-Adj", "asym-Ind-Adj-Log") & method=="QB"){
    mg <- 1 / (1 - gammaHat) - log(1 / gammaHat - 1)
    rdata <- NULL
    # B.3.1) computes the marginal empirical distribution functions
    mecdf <- apply(data, 2, ecdf)
    # B.3.2) computes the marginal empirical quantile functions
    for(i in 1:dimData[2]) rdata <- cbind(rdata, 1 - dimData[1] * mecdf[[i]](data[, i]) / (dimData[1] + 1))
    # computes the tail dependence functions
    R11 <- apply(indx, 1, estPairETC, data=rdata, ndata=dimData[1], k=k)
    Rj1 <- apply(indx, 1, estPairLeftETC, data=rdata, ndata=dimData[1],k=k)
    R1l <- apply(indx, 1, estPairRightETC, data=rdata, ndata=dimData[1],k=k)
    # computes the off diagonal covariance terms
    CovEHat <- gammaHat[indx[,1]] * gammaHat[indx[,2]] * (R11 * (mg[indx[,1]] +
               rn - 1) * (mg[indx[,2]] + rn - 1) + (mg[indx[,1]] + rn) *
               Rj1 + (mg[indx[,2]] + rn) * R1l) / rn^2
  }
  # C) fills in the variance-covariance matrix
  VarCovEHat[lower.tri(VarCovEHat)] <- CovEHat
  VarCovEHat <- t(VarCovEHat)
  VarCovEHat[lower.tri(VarCovEHat)] <- CovEHat
  # C.1) with the relative estimator the variance-covariance matrix needs
  # to be rescaled by the expectile estimator
  if(regexpr("Log", varType, fixed=TRUE)[1]==-1){
    diag(VarCovEHat) <- ExpctHat^2 * VarEHat
    CovEHat <- ExpctHat[indx[,1]] * ExpctHat[indx[,2]] * CovEHat
    VarCovEHat[lower.tri(VarCovEHat)] <- CovEHat
    VarCovEHat <- t(VarCovEHat)
    VarCovEHat[lower.tri(VarCovEHat)] <- CovEHat
  }
  # C.2) Normalised variance-covariance matrix
  VarCovEHat <- rn^2 * VarCovEHat / k
  return(VarCovEHat)
}

# computes the Quantile-Based marginal Expected Shortfall
# @ the intermediate level
QBmarExpShortF <- function(data, tau, n, q){
  res <- sum(data[,1] * as.numeric(data[,1]>0 & data[,2]>q))
  return(res / (n*(1-tau)))
}

# computes the Expectile-Based marginal Expected Shortfall
# @ the intermediate level
EBmarExpShortF <- function(data, tau, n, xi){
  res <- sum(data[,1] * as.numeric(data[,1]>0 & data[,2]>xi))
  return(res / sum(data[,2]>xi))
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
###
### START
###
################## MULTIIVARIATE CASE ##########################################

################################################################################
###
### Estimation of multiple tail indices
### using the Hill estimator
### variance-covariance matrix of the estimator
### and (1-alpha)100% confidence regions are computed
###
################################################################################
MultiHTailIndex <- function(data, k, var=FALSE, varType="asym-Dep", bias=FALSE,
                            alpha=0.05, plot=FALSE){

  # initialization
  gammaHat <- NULL
  VarGamHat <- NULL
  VarCovGHat <- NULL
  EstConReg <- NULL
  biasTerm <- NULL
  dimData <- dim(data)

  # computes multiple tail indices estimates
  res <- apply(data, 2, HTailIndex, k=k, var=var, bias=bias, varType="asym-Ind",
               bigBlock=NULL, smallBlock=NULL, alpha=alpha)

  # computes the estimator variance-covariance matrix
  if(var){
    # computes the number of distinct pairs
    for(i in 1:dimData[2]) {
      gammaHat <- c(gammaHat, as.numeric(res[[i]][1]))
      VarGamHat <- c(VarGamHat, as.numeric(res[[i]][2]))
      if(bias)  biasTerm <- c(biasTerm, as.numeric(res[[i]][4]))
    }
    # sets the off doagonal variance terms of the normalised estimator
    VarCovGHat <- diag(VarGamHat)
    # derives the covariance structure
    if(varType=="asym-Dep"){
      # compute the covariance of the normalised tail index estimator
      estAC <- estAsymCov(data, k, sqrt(VarGamHat))
      # fill in the covariance terms of the variance-covariance matrix
      VarCovGHat[lower.tri(VarCovGHat)] <- estAC
      VarCovGHat <- t(VarCovGHat)
      VarCovGHat[lower.tri(VarCovGHat)] <- estAC
      VarCovGHat <- VarCovGHat / k
    }
    # checks whether the variance-covariance matrix is well defined
    if(any(diag(VarCovGHat)<=0)){
      warning("Variance-covariance matrix is not well defined")
      VarCovGHat <- NA
      EstConReg <- NA
      return(list(gammaHat=gammaHat, VarCovGHat=VarCovGHat, EstConReg=EstConReg))
    }
    ev <- eigen(VarCovGHat, symmetric = TRUE)
    if(!all(ev$values >= 0)){
      warning("Variance-covariance matrix is numerically not positive semidefinite")
      VarCovGHat <- NA
      EstConReg <- NA
      return(list(gammaHat=gammaHat, VarCovGHat=VarCovGHat, EstConReg=EstConReg))
    }
    # 2D graphical representation of the symmetric confidence regions
    if(dimData[2]==2){
      EstConReg <- ellipse(gammaHat, VarCovGHat, alpha)
      if(plot){
        xrange <- range(EstConReg[,1])
        yrange <- range(EstConReg[,2])
        par(mai=c(.6,.6,.2,.1), mgp=c(1.5,.5,0))
        ylab <-eval(bquote(expression(widehat(gamma)[list(.(k), 2)])))
        xlab <-eval(bquote(expression(widehat(gamma)[list(.(k), 1)])))
        plot(gammaHat[1], gammaHat[2], pch=20, xlim=c(xrange[1]-.1, xrange[2]+.1),
             ylim=c(yrange[1]-.1, yrange[2]+.1), xlab=xlab, ylab=ylab,
             main="Bivariate Tail Index Estimation")
        lines(EstConReg, lwd=2, col="red")
        legend("topleft", col=c(1,2), lwd=c(2,2), cex=1.2, bty="n", c("Point estimate",
               paste((1-alpha)*100, "% Asymptotic Confidence Region", sep="")))
      }
    }
    # 3D graphical reppresentation of the symmetric confidence regions
    if(dimData[2]==3){
      EstConReg <- ellipsoid(gammaHat, VarCovGHat, alpha)
      if(plot){
        zlab <-eval(bquote(expression(widehat(gamma)[list(.(k), 3)])))
        ylab <-eval(bquote(expression(widehat(gamma)[list(.(k), 2)])))
        xlab <-eval(bquote(expression(widehat(gamma)[list(.(k), 1)])))
        scatter3D(EstConReg[,1], EstConReg[,2], EstConReg[,3], type="l", xlab="",
                  ylab="", zlab="", ticktype="detailed", main="Trivariate Tail Index Estimation")
        text(-0.2675761, -0.3988516, xlab)
        text(0.3005687, -0.3688111, ylab)
        text(-0.4494528, -0.03598391, zlab)
        points3D(gammaHat[1], gammaHat[2], gammaHat[3], pch=21, col=2, add=TRUE)
      }
    }
  }
  else for(i in 1:dimData[2]) {
    gammaHat <- c(gammaHat, as.numeric(res[[i]][1]))
    if(bias) biasTerm <- c(biasTerm, as.numeric(res[[i]][4]))
  }
  return(list(gammaHat=gammaHat,
              VarCovGHat=VarCovGHat,
              biasTerm=biasTerm,
              EstConReg=EstConReg))
}


################################################################################
###
### Estimation of multiple Expectiles @ the intermediate level
### using the LAWS and QB estimators
### variance-covariance matrix of the estimator
### and (1-alpha)100% confidence regions are computed
###
################################################################################
estMultiExpectiles <- function(data, tau, method="LAWS", tailest="Hill", var=FALSE,
                               varType="asym-Ind-Adj", k=NULL, alpha=0.05, plot=FALSE){
  # initialization
  ExpctHat <- NULL
  VarEHat <- NULL
  VarCovEHat <- NULL
  EstConReg <- NULL
  gammaHat <- NULL
  biasTerm <- NULL
  dimData <- dim(data)

  # checks whether the essential routine parameters have been inserted
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  if(isNk) k <- floor(dimData[1]*(1-tau))
  if(isNtau) tau <- 1-k/dimData[1]
  # computes multiple expectiles
  res <- apply(data, 2, estExpectiles, tau=tau, method=method, tailest=tailest,
               var=var, varType=varType, bigBlock=NULL, smallBlock=NULL, k=k,
               alpha=alpha)
  # computes the variance-covariance matrix of the expctile estimator
  if(var){
    # computes expectiles, bias terms, variance and tail indices
    for(i in 1:dimData[2]) {
      # 1) computes expectile estimates at the intermediate level for all the margins
      ExpctHat <- c(ExpctHat, as.numeric(res[[i]][1]))
      # 2) computes the bias term for all the margins
      biasTerm <- c(biasTerm, as.numeric(res[[i]][2]))
      # 3) computes estimates of the variances of expectile estimates
      VarEHat <- c(VarEHat, as.numeric(res[[i]][3]))
      # 4) computes tail index estimates for all the margins
      if(tailest=="Hill") gammaHat <- c(gammaHat, HTailIndex(data[,i], k=k)$gammaHat)
    }
    # computes the covariance terms
    VarCovEHat <- estMultiExpectVar(data, dimData, ExpctHat, gammaHat, method,
                                    k, tau, VarEHat, varType)
    #  checks whether the variance-covariance matrix is well defined
    if(any(is.na(VarCovEHat))){
      warning("Variance-covariance matrix is not well defined")
      VarCovEHat <- NA
      EstConReg <- NA
      return(list(ExpctHat=ExpctHat, biasTerm=biasTerm, VarCovEHat=VarCovEHat, EstConReg=EstConReg))
    }
    if(any(diag(VarCovEHat)<=0)){
      warning("Variance-covariance matrix is not well defined")
      VarCovEHat <- NA
      EstConReg <- NA
      return(list(ExpctHat=ExpctHat, biasTerm=biasTerm, VarCovEHat=VarCovEHat, EstConReg=EstConReg))
    }
    ev <- eigen(VarCovEHat, symmetric = TRUE)
    if(!all(ev$values >= 0)){
      warning("Variance-covariance matrix is numerically not positive semidefinite")
      VarCovEHat <- NA
      EstConReg <- NA
      return(list(ExpctHat=ExpctHat, biasTerm=biasTerm, VarCovEHat=VarCovEHat, EstConReg=EstConReg))
    }
    # computes a rescaling of the mean and variance components
    b <- 1 / (1 + biasTerm / sqrt(k))
    mu <- ExpctHat * b
    B <- diag(b)
    Sigma <- B %*% VarCovEHat %*% B
    # 2D graphical reppresentation
    if(dimData[2]==2){
      EstConReg <- ellipse(mu, Sigma, alpha)
      if(plot){
        xrange <- range(EstConReg[,1])
        yrange <- range(EstConReg[,2])
        par(mai=c(.6,.6,.2,.1), mgp=c(1.5,.5,0))
        ylab <-eval(bquote(expression(widehat(xi)[list(.(tau), 2)])))
        xlab <-eval(bquote(expression(widehat(xi)[list(.(tau), 1)])))
        plot(mu[1], mu[2], pch=20, xlim=c(xrange[1]-1, xrange[2]+1),
             ylim=c(yrange[1]-1, yrange[2]+1), xlab=xlab, ylab=ylab,
             main=eval(bquote(expression("Bivariate Expectile Estimation" ~ - ~ tau[n]==~.(tau)))))
        points(data, col="gray", pch=20)
        lines(EstConReg, lwd=2, col="red")
        legend("topleft", col=c(1,2), lwd=c(2,2), cex=1.2, bty="n", c("Point estimate",
               paste((1-alpha)*100, "% Asymptotic Confidence Region", sep="")))
      }
    }
    # 3D graphical reppresentation
    if(dimData[2]==3){
      EstConReg <- ellipsoid(mu, Sigma, alpha)
      if(plot){
        zlab <-eval(bquote(expression(widehat(xi)[list(.(tau), 3)])))
        ylab <-eval(bquote(expression(widehat(xi)[list(.(tau), 2)])))
        xlab <-eval(bquote(expression(widehat(xi)[list(.(tau), 1)])))
        scatter3D(EstConReg[,1],EstConReg[,2],EstConReg[,3], type="l", xlab="",
                  ylab="", zlab="", ticktype="detailed", main="Trivariate Expectile Estimation")
        text(-0.2675761, -0.3988516, xlab)
        text(0.3005687, -0.3688111, ylab)
        text(-0.4494528, -0.03598391, zlab)
        points3D(mu[1],mu[2],mu[3], pch=21, col=2, add=TRUE)
      }
    }
  }
  # independence case
  else for(i in 1:dimData[2]){
    # 1) computes expectile estimates at the intermediate level for all the margins
    ExpctHat <- c(ExpctHat, as.numeric(res[[i]][1]))
    # 2) computes the bias term for all the margins
    biasTerm <- c(biasTerm, as.numeric(res[[i]][2]))
  }
  return(list(ExpctHat=ExpctHat,
              biasTerm=biasTerm,
              VarCovEHat=VarCovEHat,
              EstConReg=EstConReg))
}


################################################################################
###
### Estimation of multiple Expectiles @ the extreme level
### using the LAWS and QB estimators
### variance-covariance matrix of the estimator
### and (1-alpha)100% confidence regions are computed
###
################################################################################
predMultiExpectiles <- function(data, tau, tau1, method="LAWS", tailest="Hill",
                                var=FALSE, varType="asym-Ind-Adj-Log", bias=FALSE,
                                k=NULL, alpha=0.05, plot=FALSE){
  # initialization
  ExpctHat <- NULL
  VarEHat <- NULL
  VarCovEHat <- NULL
  EstConReg <- NULL
  biasTerm <- NULL
  gammaHat <- NULL
  dimData <- dim(data)

  # checks whether the essential routine oarameters have been inserted
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  if(isNk) k <- floor(dimData[1]*(1-tau))
  if(isNtau) tau <- 1-k/dimData[1]
  # computes multiple expctiles
  res <- apply(data, 2, predExpectiles, tau=tau, tau1=tau1, method=method,
               tailest=tailest, var=var, varType=varType, bias=FALSE,
               bigBlock=NULL, smallBlock=NULL, k=k, alpha_n=NULL, alpha=alpha)
  # compute the variance-covariance of the expectile estimator
  if(var){
    # computes the number of distinct pairs
    indx <- t(combn(dimData[2],2))
    # computes expectiles, bias terms, variance and tail indices
    for(i in 1:dimData[2]) {
      # 1) computes expectile estimates at the intermediate level for all the margins
      ExpctHat <- c(ExpctHat, as.numeric(res[[i]][1]))
      # 2) computes the bias term for all the margins
      biasTerm <- c(biasTerm, as.numeric(res[[i]][2]))
      # 3) computes estimates of the variances of expectile estimates
      VarEHat <- c(VarEHat, as.numeric(res[[i]][3]))
      # 4) computes tail index estimates for all the margins
      if(tailest=="Hill") gammaHat <- c(gammaHat, HTailIndex(data[,i], k=k)$gammaHat)
    }
    # computes the covariance terms of the variance-covariance matrix
    VarCovEHat <- predMultiExpectVar(data, dimData, ExpctHat, gammaHat, method,
                                     k, tau, tau1, VarEHat, varType)
    # checks the validity of the variance-covariance matrix
    if(any(is.na(VarCovEHat))){
      warning("Variance-covariance matrix is not well defined")
      VarCovEHat <- NA
      EstConReg <- NA
      return(list(ExpctHat=ExpctHat, biasTerm=biasTerm, VarCovEHat=VarCovEHat, EstConReg=EstConReg))
    }
    if(any(diag(VarCovEHat)<=0)){
      warning("Variance-covariance matrix is not well defined")
      VarCovEHat <- NA
      EstConReg <- NA
      return(list(ExpctHat=ExpctHat, biasTerm=biasTerm, VarCovEHat=VarCovEHat, EstConReg=EstConReg))
    }
    ev <- eigen(VarCovEHat, symmetric = TRUE)
    if(!all(ev$values >= 0)){
      warning("Variance-covariance matrix is numerically not positive semidefinite")
      VarCovEHat <- NA
      EstConReg <- NA
      return(list(ExpctHat=ExpctHat, biasTerm=biasTerm, VarCovEHat=VarCovEHat, EstConReg=EstConReg))
    }
    # graphical reppresentation in the log-scale
    if(regexpr("Log", varType, fixed=TRUE)[1]==-1){
      cn <- sqrt(k) / log((1-tau)/(1-tau1))
      b <- 1 / (1 + biasTerm / cn)
      mu <- ExpctHat * b
      B <- diag(b)
      Sigma <- B %*% VarCovEHat %*% B
      # 2D graphical representation of the confidence regions
      if(dimData[2]==2){
        EstConReg <- ellipse(mu, Sigma, alpha)
        if(plot){
          xrange <- range(EstConReg[,1])
          yrange <- range(EstConReg[,2])
          par(mai=c(.6,.6,.2,.1), mgp=c(1.5,.5,0))
          ylab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 2)])))
          xlab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 1)])))
          plot(mu[1], mu[2], pch=20, xlim=c(xrange[1]-1, xrange[2]+1),
               ylim=c(yrange[1]-1, yrange[2]+1), xlab=xlab, ylab=ylab,
               main="Bivariate Expectile Estimation")
          lines(EstConReg, lwd=2, col="red")
          legend("topleft", col=c(1,2), lwd=c(2,2), cex=1.2, bty="n", c("Point estimate",
                 paste((1-alpha)*100, "% Asymptotic Confidence Region", sep="")))
        }
      }
      # 3D graphical representation of the confidence regions
      if(dimData[2]==3){
        EstConReg <- ellipsoid(mu, Sigma, alpha)
        if(plot){
          zlab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 3)])))
          ylab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 2)])))
          xlab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 1)])))
          scatter3D(EstConReg[,1],EstConReg[,2],EstConReg[,3], type="l", xlab="",
                    ylab="", zlab="", ticktype="detailed", main="Trivariate Expectile Estimation")
          text(-0.2675761, -0.3988516, xlab)
          text(0.3005687, -0.3688111, ylab)
          text(-0.4494528, -0.03598391, zlab)
          points3D(mu[1],mu[2],mu[3], pch=21, col=2, add=TRUE)
        }
      }
    }
    # graphical representation in relative scale
    else{
      cn <- sqrt(k) / log((1-tau)/(1-tau1))
      mu <- biasTerm / cn
      Sigma <- VarCovEHat
      # 2D graphical representation of the confidence regions
      if(dimData[2]==2){
        EH <- apply(array(ExpctHat, c(1,dimData[2])), 2, rep, times=250)
        EstConReg <-  EH * exp(ellipse(mu, Sigma, alpha))
        mu <- ExpctHat * exp(mu)
        if(plot){
          xrange <- range(EstConReg[,1])
          yrange <- range(EstConReg[,2])
          par(mai=c(.6,.6,.2,.1), mgp=c(1.5,.5,0))
          ylab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 2)])))
          xlab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 1)])))
          plot(mu[1], mu[2], pch=20, xlim=c(xrange[1]-1, xrange[2]+1),
               ylim=c(yrange[1]-1, yrange[2]+1), xlab=xlab, ylab=ylab,
               main="Bivariate Expectile Estimation")
          lines(EstConReg, lwd=2, col="red")
          legend("topleft", col=c(1,2), lwd=c(2,2), cex=1.2, bty="n", c("Point estimate",
                 paste((1-alpha)*100, "% Asymptotic Confidence Region", sep="")))
        }
      }
      # 3D graphical representation of the confidence regions
      if(dimData[2]==3){
        EH <- apply(array(ExpctHat, c(1,dimData[2])), 2, rep, times=3600)
        EstConReg <- EH * exp(ellipsoid(mu, Sigma, alpha))
        mu <- ExpctHat * exp(mu)
        if(plot){
          zlab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 3)])))
          ylab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 2)])))
          xlab <-eval(bquote(expression(widehat(xi)[list(.(tau1), 1)])))
          scatter3D(EstConReg[,1],EstConReg[,2],EstConReg[,3], type="l", xlab="",
                    ylab="", zlab="", ticktype="detailed", main="Trivariate Expectile Estimation")
          text(-0.2675761, -0.3988516, xlab)
          text(0.3005687, -0.3688111, ylab)
          text(-0.4494528, -0.03598391, zlab)
          points3D(mu[1],mu[2],mu[3], pch=21, col=2, add=TRUE)
        }
      }
    }
  }
  else for(i in 1:dimData[2]){
    # 1) computes expectile estimates at the intermediate level for all the margins
    ExpctHat <- c(ExpctHat, as.numeric(res[[i]][1]))
    # 2) computes the bias term for all the margins
    biasTerm <- c(biasTerm, as.numeric(res[[i]][2]))
  }
  return(list(ExpctHat=ExpctHat,
              biasTerm=biasTerm,
              VarCovEHat=VarCovEHat,
              EstConReg=EstConReg))
}

################################################################################
###
### Estimation of multiple quantiles @ the extreme level
### using the LAWS and QB estimators
### variance-covariance matrix of the estimator
### and (1-alpha)100% confidence regions are computed
###
################################################################################
extMultiQuantile <- function(data, tau, tau1, var=FALSE, varType="asym-Ind-Log",
                             bias=FALSE, k=NULL, alpha=0.05, plot=FALSE){
  # initialization
  ExtQHat <- NULL
  VarExQHat <- NULL
  VarCovExQHat <- NULL
  EstConReg <- NULL
  dimData <- dim(data)

  # checks whether the essential routine parameters have been inserted
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  if(isNk) k <- floor(dimData[1]*(1-tau))
  if(isNtau) tau <- 1-k/dimData[1]
  cn <- sqrt(k) / log((1-tau)/(1-tau1))
  # computes multiple extreme quantiles
  res <- apply(data, 2, extQuantile, tau=tau, tau1=tau1, var=var, varType=varType,
               bias=FALSE, bigBlock=NULL, smallBlock=NULL, k=k, alpha=alpha)
  # computes the variance-covariance matrix of estimator
  if(var){
    # computes the number of distinct pairs
    indx <- t(combn(dimData[2],2))
    # computes quantiles, bias terms, variance and tail indices
    for(i in 1:dimData[2]) {
      # 1) computes quantile estimates at the extreme level for all the margins
      ExtQHat <- c(ExtQHat, as.numeric(res[[i]][1]))
      # 3) computes estimates of the variances of expectile estimates
      VarExQHat <- c(VarExQHat, as.numeric(res[[i]][2]))
    }
    # sets the variances of the normalised estimator
    VarCovExQHat <- diag(VarExQHat)
    # derives the covariance structure
    # compute the covariance of the relative quantile estimator
    estAC <- estAsymCov(data, k, sqrt(VarExQHat))
    # fills in the covariance terms of the variance-covariance matrix
    VarCovExQHat[lower.tri(VarCovExQHat)] <- estAC
    VarCovExQHat <- t(VarCovExQHat)
    VarCovExQHat[lower.tri(VarCovExQHat)] <- estAC
    VarCovExQHat <- VarCovExQHat / cn

    # checks the validity of the variance-covariance matrix
    if(any(is.na(VarCovExQHat))){
      warning("Variance-covariance matrix is not well defined")
      VarCovExQHat <- NA
      EstConReg <- NA
      return(list(ExtQHat=ExtQHat, VarCovExQHat=VarCovExQHat, EstConReg=EstConReg))
    }
    if(any(diag(VarCovExQHat)<=0)){
      warning("Variance-covariance matrix is not well defined")
      VarCovExQHat <- NA
      EstConReg <- NA
      return(list(ExtQHat=ExtQHat, VarCovExQHat=VarCovExQHat, EstConReg=EstConReg))
    }
    ev <- eigen(VarCovExQHat, symmetric = TRUE)
    if(!all(ev$values >= 0)){
      warning("Variance-covariance matrix is numerically not positive semidefinite")
      VarCovExQHat <- NA
      EstConReg <- NA
      return(list(ExtQHat=ExtQHat, VarCovExQHat=VarCovExQHat, EstConReg=EstConReg))
    }
    # graphical reppresentation of the estimation results in the log-scale
    if(regexpr("Log", varType, fixed=TRUE)[1]==-1){
      mu <- ExtQHat
      B <- diag(mu)
      VarCovExQHat <- B %*% VarCovExQHat %*% B
      Sigma <- VarCovExQHat
      # 2D graphical reppresentation of the confidence regions
      if(dimData[2]==2){
        EstConReg <- ellipse(mu, Sigma, alpha)
        if(plot){
          xrange <- range(EstConReg[,1])
          yrange <- range(EstConReg[,2])
          par(mai=c(.6,.6,.2,.1), mgp=c(1.5,.5,0))
          ylab <-eval(bquote(expression(widehat(q)[list(.(tau1), 2)])))
          xlab <-eval(bquote(expression(widehat(q)[list(.(tau1), 1)])))
          plot(mu[1], mu[2], pch=20, xlim=c(xrange[1]-1, xrange[2]+1),
               ylim=c(yrange[1]-1, yrange[2]+1), xlab=xlab, ylab=ylab,
               main="Bivariate Quantile Estimation")
          lines(EstConReg, lwd=2, col="red")
          legend("topleft", col=c(1,2), lwd=c(2,2), cex=1.2, bty="n", c("Point estimate",
                 paste((1-alpha)*100, "% Asymptotic Confidence Region", sep="")))
        }
      }
      # 3D graphical reppresentation of the confidence regions
      if(dimData[2]==3){
        EstConReg <- ellipsoid(mu, Sigma, alpha)
        if(plot){
          zlab <-eval(bquote(expression(widehat(q)[list(.(tau1), 3)])))
          ylab <-eval(bquote(expression(widehat(q)[list(.(tau1), 2)])))
          xlab <-eval(bquote(expression(widehat(q)[list(.(tau1), 1)])))
          scatter3D(EstConReg[,1],EstConReg[,2],EstConReg[,3], type="l", xlab="",
                    ylab="", zlab="", ticktype="detailed", main="Trivariate Quantile Estimation")
          text(-0.2675761, -0.3988516, xlab)
          text(0.3005687, -0.3688111, ylab)
          text(-0.4494528, -0.03598391, zlab)
          points3D(mu[1],mu[2],mu[3], pch=21, col=2, add=TRUE)
        }
      }
    }
    # graphical reppresentation of the estimation results in the relative scale
    else{
      mu <- rep(0, dimData[2])
      Sigma <- VarCovExQHat
      # 2D graphical reppresentation of the confidence regions
      if(dimData[2]==2){
        EQH <- apply(array(ExtQHat, c(1,dimData[2])), 2, rep, times=250)
        EstConReg <-  EQH * exp(ellipse(mu, Sigma, alpha))
        if(plot){
          xrange <- range(EstConReg[,1])
          yrange <- range(EstConReg[,2])
          par(mai=c(.6,.6,.2,.1), mgp=c(1.5,.5,0))
          ylab <-eval(bquote(expression(widehat(q)[list(.(tau1), 2)])))
          xlab <-eval(bquote(expression(widehat(q)[list(.(tau1), 1)])))
          plot(mu[1], mu[2], pch=20, xlim=c(xrange[1]-1, xrange[2]+1),
               ylim=c(yrange[1]-1, yrange[2]+1), xlab=xlab, ylab=ylab,
               main="Bivariate Quantile Estimation")
          lines(EstConReg, lwd=2, col="red")
          legend("topleft", col=c(1,2), lwd=c(2,2), cex=1.2, bty="n", c("Point estimate",
                 paste((1-alpha)*100, "% Asymptotic Confidence Region", sep="")))
        }
      }
      # 3D graphical reppresentation of the confidence regions
      if(dimData[2]==3){
        EQH <- apply(array(ExtQHat, c(1,dimData[2])), 2, rep, times=3600)
        EstConReg <- EQH * exp(ellipsoid(mu, Sigma, alpha))
        mu <- ExtQHat
        if(plot){
          zlab <-eval(bquote(expression(widehat(q)[list(.(tau1), 3)])))
          ylab <-eval(bquote(expression(widehat(q)[list(.(tau1), 2)])))
          xlab <-eval(bquote(expression(widehat(q)[list(.(tau1), 1)])))
          scatter3D(EstConReg[,1],EstConReg[,2],EstConReg[,3], type="l", xlab="",
                    ylab="", zlab="", ticktype="detailed", main="Trivariate Quantile Estimation")
          text(-0.2675761, -0.3988516, xlab)
          text(0.3005687, -0.3688111, ylab)
          text(-0.4494528, -0.03598391, zlab)
          points3D(mu[1],mu[2],mu[3], pch=21, col=2, add=TRUE)
        }
      }
    }
  }
  else for(i in 1:dimData[2]){
    # 1) computes quantile estimates at the intermediate level for all the margins
    ExtQHat <- c(ExtQHat, as.numeric(res[[i]][1]))
  }
  return(list(ExtQHat=ExtQHat,
              VarCovExQHat=VarCovExQHat,
              EstConReg=EstConReg))
}

################################################################################
###
### Wald-type hypothesis testing with test statistics based on the
### LAWS, QB expectile estimators, quantile estimator and tail index estimator
### the observed statistics tests together with the chi-square critical value
### are computed
###
################################################################################
HypoTesting <- function(data, tau, tau1=NULL, type="ExpectRisks", level="extreme",
                        method="LAWS", bias=FALSE, k=NULL, alpha=0.05){
  # initialization
  ExpctHat <- NULL
  VarCovEHat <- NULL

  dimData <- dim(data)
  ones <- array(1, c(dimData[2],1))
  biasTerm <- rep(0, dimData[2])
  critVal <- qchisq(1-alpha, dimData[2]-1)

  # checks whether the essential routine parameters have been inserted
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  if(isNk) k <- floor(dimData[1]*(1-tau))
  if(isNtau) tau <- 1-k/dimData[1]

  # Wald-type statistics based on the expectile estimator
  # @ the intermediate level
  if(type=="ExpectRisks"){
    # estimation expectiles point estimates and their variance-covariance matrix
    if(level=="inter"){
      res <- estMultiExpectiles(data, tau,  method, var=TRUE, k=k)
      # checks if the variance-covariance is well defined
      if(any(is.na(res$VarCovEHat))) return(list(logLikR=NA, critVal=critVal))
      # correct the estimator and its variance-covariance matrix for the bias term
      b <- 1 / (1 + res$biasTerm / sqrt(k))
      ExpctHat <- array(res$ExpctHat * b, c(dimData[2], 1))
      B <- diag(b)
      VarCovEHat <- B %*% res$VarCovEHat %*% B
    }
    # Wald-type statistics based on the expectile estimator
    # @ the extreme level
    if(level=="extreme"){
      res <- predMultiExpectiles(data, tau, tau1, method, var=TRUE,
                                 varType="asym-Ind-Adj-Log", k=k)
      # checks if the variance-covariance is well defined
      if(any(is.na(res$VarCovEHat))) return(list(logLikR=NA, critVal=critVal))
      cn <- sqrt(k) / log((1-tau)/(1-tau1))
      ExpctHat <- array(log(res$ExpctHat) - res$biasTerm / cn, c(dimData[2], 1))
      VarCovEHat <- res$VarCovEHat
    }
  }
  # Wald-type statistics based on the extreme quantile estimator
  if(type=="QuantRisks"){
    res <- extMultiQuantile(data, tau, tau1, var=TRUE, varType="asym-Ind-Log",
                              k=k)
    # checks if the variance-covariance is well defined
    if(any(is.na(res$VarCovExQHat))) return(list(logLikR=NA, critVal=critVal))
    ExpctHat <- array(log(res$ExtQHat), c(dimData[2], 1))
    VarCovEHat <- res$VarCovExQHat
  }
  # Wald-type statistics based on the tail index estimator
  if(type=="tails"){
    res <- MultiHTailIndex(data, k, var=TRUE, varType="asym-Dep", bias=bias,
                           alpha=alpha)
    ExpctHat <- array(res$gammaHat, c(dimData[2], 1))
    if(any(is.na(res$VarCovGHat))) return(list(logLikR=NA, critVal=critVal))
    VarCovEHat <- res$VarCovGHat
  }
  # computes the inverse of the estimator variance-covariance matrix
  InvVC <- try(solve(VarCovEHat), silent=TRUE)
  if(!is.matrix(InvVC)) return(list(logLikR=NA, critVal=critVal))
  # compute the mean under the null hypothesis
  ms <- ((t(ExpctHat) %*% InvVC) %*% ones) / ((t(ones) %*% InvVC) %*% ones)
  # centered estimator
  SExpctHat <- ExpctHat - array(ms, c(dimData[2],1))
  # computes the log-likelihood ratio-test statistic
  logLikR <- as.numeric(t(SExpctHat) %*% InvVC %*% SExpctHat)

  return(list(logLikR=logLikR, critVal=critVal))
}


################################################################################
###
### Estimation of the Quantile-Based marginal
### Expected Shortfall
### @ the extreme level
###
################################################################################
QuantMES <- function(data, tau, tau1, var=FALSE, varType="asym-Dep", bias=FALSE,
                     bigBlock=NULL, smallBlock=NULL, k=NULL, alpha=0.05){
  # initialization
  VarHatQMES <- NULL
  CIHatQMES <- NULL
  CIHatQMES <- NULL

  # main body:
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  # computes the sample size
  ndata <- nrow(data)
  if(isNk) k <- floor(ndata*(1-tau))
  if(isNtau) tau <- 1-k/ndata

  # estimation of the quantile @ the intermediate level based on the empirical quantile
  QHat <- as.numeric(quantile(data[,2], tau))
  # estimation of the tail index and related quantities using the Hill estimator
  if(varType=="asym-Alt-Dep") estHill <- HTailIndex(data[,1], k)
  else estHill <- HTailIndex(data[,1], k, var, varType, bias, bigBlock, smallBlock, alpha)
  # computes an estimate of the tail index with a bias-correction
  gammaHat <- estHill$gammaHat - estHill$BiasGamHat
  # estimation of the QB marginal Expected Shortfall @ the intermediate level
  QMESt <- QBmarExpShortF(data, tau, ndata, QHat)
  # estimation of the QB marginal Expected Shortfall @ the intermediate level
  QMESt1 <- ((1-tau1)/(1-tau))^(-gammaHat) * QMESt
  # estimation of the asymptotic variance of the Hill estimator
  if(var){
    # The default approach for computing the asymptotic variance with serial dependent observations
    # is the method proposed by Drees (2003). In this case it is assumed that there is no bias term
    # If it is assumed that the Hill estimator requires a bias correction then the the asymptotic
    # variance is estimated after correcting the tail index estimate by the bias correction
    VarHatQMES <- estHill$VarGamHat

    if((varType=="asym-Alt-Dep") & (!bias)){
      # Drees (2003) approach
      j <- max(2, ceiling(ndata*(1-tau1)))
      VarHatQMES <- DHVar(data, tau, tau1, j, k, ndata)
    }
    # compute lower and upper bounds of the (1-alpha)% CI
    K <- sqrt(VarHatQMES)*log((1-tau)/(1-tau1))/sqrt(k)
    lbound <- QMESt1 * exp(qnorm(alpha/2)*K)
    ubound <- QMESt1 * exp(qnorm(1-alpha/2)*K)
    CIHatQMES <- c(lbound, ubound)
  }
  return(list(HatQMES=QMESt1,
              VarHatQMES=VarHatQMES,
              CIHatQMES=CIHatQMES))
}
################################################################################
###
### Estimation of the Expectile-Based marginal
### Expected Shortfall
### @ the extreme level
###
################################################################################
ExpectMES <- function(data, tau, tau1, method="LAWS", var=FALSE, varType="asym-Dep",
                      bias=FALSE, bigBlock=NULL, smallBlock=NULL, k=NULL,
                      alpha_n=NULL, alpha=0.05){
  # initialization
  VarHatXMES <- NULL
  CIHatXMES <- NULL
  CIHatXMES <- NULL
  # main body:
  isNk <- is.null(k)
  isNtau <- is.null(tau)
  if(isNk & isNtau) stop("Enter a value for at least one of the two parameters 'tau' and 'k' ")
  # compute the sample size
  ndata <- nrow(data)
  if(isNk) k <- floor(ndata*(1-tau))
  if(isNtau) tau <- 1-k/ndata

  # estimation of the tail index for X using the Hill estimator
  estHill <- HTailIndex(data[,1], k, var, varType, bias, bigBlock, smallBlock, alpha)
  gammaHatX <- estHill$gammaHat - estHill$BiasGamHat
  # estimation of the tail index for Y using the Hill estimator
  gammaHatY <- HTailIndex(data[,2], k)$gammaHat
  # estimation of the extreme level if requested
  if(is.null(tau1)) tau1 <- estExtLevel(alpha_n, gammaHat=gammaHatY)$tauHat
  # expectile-Based Esitmation
  if(method=="LAWS"){
    ExpctHat <- estExpectiles(data[,2], tau)$ExpctHat
    # estimation of the EB marginal Expected Shortfall @ the intermediate level
    XMESt <- EBmarExpShortF(data, tau, ndata, ExpctHat)
    # estimation of the Expectile-EB marginal Expected Shortfall @ the extreme level
    XMESt1 <- ((1-tau1)/(1-tau))^(-gammaHatX) * XMESt
  }
  # Quantile-Based Estimation
  if(method=="QB"){
    # estimation of the QB marginal Expected Shortfall @ the intermediate level
    QMESt <- QuantMES(data, NULL, tau1, k=k)$HatQMES
    # estimation of the Expectile-QB marginal Expected Shortfall @ the extreme level
    XMESt1 <- (1/gammaHatY - 1)^(-gammaHatX) * QMESt
  }
  # compute an estimate of the asymptotic variance of the expecile estimator at the extreme level
  if(var){
    # computes the asymptotic variance for independent and serial dependent data
    VarHatXMES <- estHill$VarGamHat
    # computes the "margin error"
    K <- sqrt(VarHatXMES)*log((1-tau)/(1-tau1))/sqrt(k)
    # compute lower and upper bounds of the (1-alpha)% CI
    lbound <- XMESt1 * exp(qnorm(alpha/2)*K)
    ubound <- XMESt1 * exp(qnorm(1-alpha/2)*K)
    # defines the (1-alpha)% CI
    CIHatXMES <- c(lbound, ubound)
  }
  return(list(HatXMES=XMESt1,
              VarHatXMES=VarHatXMES,
              CIHatXMES=CIHatXMES))
}


################################################################################
### END
###
################## MULTIIVARIATE CASE ##########################################


################################################################################
### END
### Main-routines (VISIBLE FUNCTIONS)
###
################################################################################
