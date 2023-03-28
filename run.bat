docker cp "%1.java" "pedantic_darwin:/JJBMC/%1.java"
docker exec pedantic_darwin java -jar JJBMC.jar -tr "%1.java" %2