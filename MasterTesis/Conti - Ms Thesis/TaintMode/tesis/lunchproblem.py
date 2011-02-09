        user = web.input().user
        meal = web.input().meal
        # save it to the file of the day
        dayfile = datetime.today().strftime('%Y-%m-%d') + '.txt'
        os.system("echo " + meal + " >> " + dayfile)
