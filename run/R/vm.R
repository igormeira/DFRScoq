l1 <- c(76.923077)
df = data.frame(l1)

par(cex.lab=1.6)# is for y-axis
par(cex.axis=1.6) # is for x-axis

boxplot(df,
at = c(1),
names = c("1x Sample"),
xlab = "Number of calls to Sample",
ylab = "Mutation score",
ylim = c(0, 100)
)