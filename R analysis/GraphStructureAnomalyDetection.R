# Specify csv file with two columns: Nodes, Edges

if(file=="") {
  stop(simpleError("CSV source file not specified. Please specify by assigning file<-'source file'"));
}

# Data
data<-read.csv(file)

pdf=TRUE
if(isTRUE(pdf)) {
pdf("nodes.pdf",width=10,height=7)
}

library(MASS)


#====================================================================
print("===========Nodes=============")
# Nodes
if(var(data$Nodes) == 0) {
print("No variance in number of nodes!")
} else {
glmres.pois<-glm(data$Nodes~1, family="poisson")
glmres.nb<-glm.nb(data$Nodes~1)

data.t<-max(data$Nodes)-data$Nodes
glmres.t.pois<-glm(data.t~1, family="poisson")
glmres.t.nb<-glm.nb(data.t~1)


# Compare fits
if(glmres.t.pois$aic < glmres.pois$aic && glmres.t.pois$aic < glmres.nb$aic) {
	if(glmres.t.nb$aic < glmres.t.pois$aic) {
		print("Zero-inflated Negative Binomial is better fit!")
		type<-4
	} else {
 		print("Zero-inflated Poisson is better fit!")
		type<-3
	}
} 
else {
	if(glmres.pois$aic < glmres.nb$aic) {
		print("Poisson is better fit")
		type<-1
	} else {
		print("Negative binomial is better fit")
		type<-2
	}
}



# Maximum Likelihood Estimation (MLE) of parameters
poires<-fitdistr(data$Nodes, "poisson")
#nbres<-fitdistr(data$Nodes, "negative binomial")
poi.t.res<-fitdistr(data.t, "poisson")
nb.t.res<-fitdistr(data.t, "negative binomial")

# Graph comparison
par(mar=c(4.3,4.3,.3,1)) 
density_P<-dpois(seq(0,10000),lambda=poires$estimate[1])
#density_NB<-dnbinom(seq(0,10000),size=nbres$estimate[1],mu=nbres$estimate[2])
max_density<-max(density(data$Nodes)$y)

if(type <= 2) {
	if(max_density < max(density_P)){
		hist(data$Nodes, freq=F,ylim=c(0,max(density_P)),xlab="Number of Nodes",main="",cex.axis=1, cex.lab=1)
	} else {
		hist(data$Nodes, freq=F,xlab="Number of Nodes",main="",cex.axis=1, cex.lab=1)

	}

lines(density_P,col="red")
lines(density_NB,col="blue")
lnb<-qnbinom(0.025,size=nbres$estimate[1],mu=nbres$estimate[2])
unb<-qnbinom(0.975,size=nbres$estimate[1],mu=nbres$estimate[2])
lp<-qpois(0.025,lambda=poires$estimate[1])
up<-qpois(0.975,lambda=poires$estimate[1])

abline(v=lnb,col="purple",lty=2)
abline(v=unb,col="purple",lty=2)
abline(v=lp,col="darkgreen",lty=2)
abline(v=up,col="darkgreen",lty=2)
plab<-paste("Poisson ( Lambda:", round(poires$estimate[1],2),"AIC:",round(glmres.pois$aic,0),")")
nblab<-paste("Negative Binomial ( Size:", round(nbres$estimate[1],2)," Mu:",round(nbres$estimate[2],2)," AIC:",round(glmres.nb$aic,0),")")
legend("topright",col=c("red","blue","darkgreen","purple"),legend=c(plab,nblab,"Poisson 2.5% cutoff","Negative Binomial 2.5% cutoff"),lty=c(1,1,2,2),merge=TRUE)

outliers.1<-data$Nodes > up
outliers.2<-data$Nodes < lp
p.outliers<-outliers.1 | outliers.2

outliers.1<-data$Nodes > unb
outliers.2<-data$Nodes < lnb
nb.outliers<-outliers.1 | outliers.2

freq<-table(data$Nodes)
prop<-freq/length(data$Nodes) < 0.05

outliers<-function(freq,prop) {
	count<-0
	for(i in 1:length(freq)) {
		if(isTRUE(as.vector(prop[i]))) count<-(as.vector(freq)[i])+count
	}
	return(count)
}

p.outliers.str<-paste("Number of outliers using Poisson: ", table(p.outliers)["TRUE"]) 
nb.outliers.str<-paste("Number of outliers using Negative Binomial: ", table(nb.outliers)["TRUE"]) 
prop.outliers.str<-paste("Number of outliers using Proportion: ", outliers(freq,prop)) 

print(p.outliers.str)
print(nb.outliers.str)
print(prop.outliers.str)




} else {
	density_PT<-dpois(seq(0,10000),lambda=poi.t.res$estimate[1])
	density_NBT<-dnbinom(seq(0,10000),size=nb.t.res$estimate[1],mu=nb.t.res$estimate[2])
	max_density_t<-max(density(data.t)$y)

#	if(max_density_t < max(density_PT)){
#		hist(data.t, freq=F,ylim=c(0,max(density_PT)),xlab="Number of Nodes (using zero-inflated model)",main="",cex=0.7)
#	} else {
		hist(data.t, freq=F,xlab="Number of Nodes (using zero-inflated model)",main="",cex=0.7)
#	}


	lines(density_PT,col="red")
	lines(density_NBT,col="blue")
	
	lp<-qpois(0.05,lambda=poi.t.res$estimate[1])
	up<-qpois(0.95,lambda=poi.t.res$estimate[1])


	lnb<-qnbinom(0.05,size=nb.t.res$estimate[1],mu=nb.t.res$estimate[2])
	unb<-qnbinom(0.95,size=nb.t.res$estimate[1],mu=nb.t.res$estimate[2])

	abline(v=lnb,col="purple",lty=2)
	abline(v=unb,col="purple",lty=2)
	
	abline(v=lp,col="darkgreen",lty=2)
	abline(v=up,col="darkgreen",lty=2)
	plab<-paste("Zero-Inflated Poisson ( Lambda:", round(poi.t.res$estimate[1],2)," AIC:",round(glmres.t.pois$aic,2),")")
	nblab<-paste("Zero-Inflated Negative Binomial ( Size:", round(nb.t.res$estimate[1],2)," Mu:",round(nb.t.res$estimate[2],2)," AIC:",round(glmres.t.nb$aic,2),")")

	legend("topright",col=c("red","blue","darkgreen","purple"),legend=c(plab,nblab,"Zero-Inflated Poisson 5% cutoff","Zero-Inflated Negative Binomial 5% cutoff"),lty=c(1,1,2,2),merge=TRUE)
	outliers.1<-data.t > up
	outliers.2<-data.t < lp
	p.outliers<-outliers.1 | outliers.2

	outliers.1<-data.t > unb
	outliers.2<-data.t < lnb
	nb.outliers<-outliers.1 | outliers.2

	freq<-table(data.t)
	prop<-freq/length(data.t) < 0.05

	outliers<-function(freq,prop) {
	count<-0
	for(i in 1:length(freq)) {
		if(isTRUE(as.vector(prop[i]))) count<-(as.vector(freq)[i])+count
	}
	return(count)
}

	p.outliers.str<-paste("Number of outliers using Zero-Inflated Poisson: ", table(p.outliers)["TRUE"]) 
	nb.outliers.str<-paste("Number of outliers using Zero-Inflated Negative Binomial: ", table(nb.outliers)["TRUE"]) 	
	prop.outliers.str<-paste("Number of outliers using Proportion: ", outliers(freq,prop)) 


	print(p.outliers.str)
	print(nb.outliers.str)
	print(prop.outliers.str)
}


}

print("=============================")

if(isTRUE(pdf)) dev.off()


# Edges
if(isTRUE(pdf)) {
pdf("edges.pdf",width=10,height=7)
}


library(MASS)
#data$Edges<-data$Edges-min(data$Edges)

print("===========Egdes=============")
# Edges
if(var(data$Edges) == 0) {
print("No variance in number of edges!")
} else {
glmres.pois<-glm(data$Edges~1, family="poisson")
glmres.nb<-glm.nb(data$Edges~1)


if(glmres.pois$aic < glmres.nb$aic) {
	print("Poisson is better fit")
} else print("Negative binomial is better fit")


# Maximum Likelihood Estimation (MLE) of parameters
poires<-fitdistr(data$Edges, "poisson")
nbres<-fitdistr(data$Edges, "negative binomial")

# Graph comparison
par(mar=c(4.3,4.3,.3,1)) 

density_P<-dpois(seq(0,10000),lambda=poires$estimate[1])
density_NB<-dnbinom(seq(0,10000),size=nbres$estimate[1],mu=nbres$estimate[2])
max_density<-max(density(data$Edges)$y)

hist(data$Edges, freq=F,ylim=c(0,max(density_P)),xlab="Number of Edges",main="",cex.axis=1, cex.lab=1)

lines(density_P,col="red")
lines(density_NB,col="blue")
lnb<-qnbinom(0.025,size=nbres$estimate[1],mu=nbres$estimate[2])
unb<-qnbinom(0.975,size=nbres$estimate[1],mu=nbres$estimate[2])
lp<-qpois(0.025,lambda=poires$estimate[1])
up<-qpois(0.975,lambda=poires$estimate[1])

abline(v=lnb,col="purple",lty=2)
abline(v=unb,col="purple",lty=2)
abline(v=lp,col="darkgreen",lty=2)
abline(v=up,col="darkgreen",lty=2)
plab<-paste("Poisson ( Lambda:", round(poires$estimate[1],2),"AIC:",round(glmres.pois$aic,0),")")
nblab<-paste("Negative Binomial ( Size:", round(nbres$estimate[1],0)," Mu:",round(nbres$estimate[2],2)," AIC:",round(glmres.nb$aic,0),")")
legend("topright",col=c("red","blue","darkgreen","purple"),legend=c(plab,nblab,"Poisson 2.5% cutoff","Negative Binomial 2.5% cutoff"),lty=c(1,1,2,2),merge=TRUE)

outliers.1<-data$Edges > up
outliers.2<-data$Edges < lp
p.outliers<-outliers.1 | outliers.2

outliers.1<-data$Edges > unb
outliers.2<-data$Edges < lnb
nb.outliers<-outliers.1 | outliers.2

freq<-table(data$Edges)
prop<-freq/length(data$Edges) < 0.05



p.outliers.str<-paste("Number of outliers using Poisson: ", table(p.outliers)["TRUE"]) 
nb.outliers.str<-paste("Number of outliers using Negative Binomial: ", table(nb.outliers)["TRUE"]) 
prop.outliers.str<-paste("Number of outliers using Proportion: ", outliers(freq,prop)) 

print(p.outliers.str)
print(nb.outliers.str)
print(prop.outliers.str)
}

print("=============================")

if(isTRUE(pdf)) dev.off()