l1 <- c(75.537634,75.268817,75.537634,72.043011,75.537634)
l5 <- c(75.537634,75.537634,75.537634,75.537634,75.537634)
l10 <- c(75.537634,75.537634,75.537634,75.537634,75.537634)
df = data.frame(l1,l5,l10)

par(cex.lab=1.6)# is for y-axis
par(cex.axis=1.6) # is for x-axis

boxplot(df,
at = c(1,2,3),
names = c("1x Sample","5x Sample","10x Sample"),
xlab = "Number of calls to Sample",
ylab = "Mutation score",
ylim = c(0, 100)
)