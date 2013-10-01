import History

main = do
    history <- parseHistory
    print $ take 10 history
