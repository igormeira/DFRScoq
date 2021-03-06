l1 <- c(53.407821,55.642458,58.100559,58.212291,58.659218)
l5 <- c(58.659218,60.335196,60.111732,59.888268,58.659218)
l10 <- c(60.335196,58.882682,59.441341,60.223464,60.335196)
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